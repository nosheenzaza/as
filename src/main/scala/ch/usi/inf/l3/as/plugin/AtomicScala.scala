/*
 * No license yet selected
 * 
 */
package ch.usi.inf.l3.as.plugin

import scala.tools.nsc
import nsc.Global
import nsc.Phase
import nsc.plugins.Plugin
import nsc.plugins.PluginComponent
import scala.tools.nsc.transform.Transform
import scala.tools.nsc.transform.TypingTransformers
import scala.tools.nsc.ast.TreeDSL
import scala.annotation.StaticAnnotation
import scala.collection.mutable.Map
import scala.reflect.internal.Flags._

/**
 * A port of Vaziri's 2012 proposal of Atomic sets for Scala
 * @author Nosheen Zaza
 *
 * General Notes and Considerations:
 * 1- I am using scala annotations at the moment because I want to be able to
 * use annotations everywhere. The negative side is that they are not available
 * at runtime in case I needed this in the future. I might change this decision
 * later. This code contains some extra, unused functions to support Java
 * annotations in case I needed to do so.
 *
 * General TODO:
 * 1- Support annotating fields declared in a class constructor, this requires
 * adding another phase that catches the @atomic annotation before the
 * compiler disposes it for good, this should be done after the parser
 * phase.
 * 2- Forgot to map classes to atomic sets in their parents. Do this at
 * some point.
 * 3- use the real lock object with lock ordering
 * 4- Support module classes and traits
 * 5- I am only considering one atomic set per class at the moment.
 * 6- Add type checking
 * 7- When supporting multiple locks, I need to insert an array
 * of locks of type OderedLock instead of Object as the lock
 */
class AtomicScala(val global: Global) extends Plugin {

  import global._

  val name = "atomic-scala"
  val description = "Atomic sets for Scala"
  val components = List[PluginComponent](CheckAnnotationTargets,
    ClassSetsMapping,
    AddLockFields, AddSync)

  type GlobalType = this.global.type

  /**
   * TODO later for optimizations, I will need to relate sets to fields and not
   * only to classes.
   */
  val classSetsMap = Map[Symbol, List[String]]()

  /**
   * base name for lock fields
   */
  val as_lock = "__as_lock"

  /**
   * Class of the lock object to be used
   */
  val lockClass = "ch.usi.inf.l3.as.plugin.OrderedLock"

  /******************************* Utilities ************************************/

  /**
   * Get the symbol of the object to be used as a lock object.
   * TODO I think am invoking this with the wrong param somewhere!
   */
  def getLockSym(name: String) =
    rootMirror.getClassByName(newTypeName(name))

  /**
   * pre: the tree has an owner.
   */
  def ownerIsClass(t: Tree) = t.symbol.owner.isClass

  def annotationList(t: Tree) =
    if (hasSymbol(t)) Some(t.symbol.annotations) else None

  def atomicAnnotation(annList: List[AnnotationInfo]) = {
    /* Need to change to ch.usi.inf.l3.ascala.Atomic if I want to use
         * java annotations 
         */
    val atomicSymbol =
      rootMirror.getClass(newTypeName("ch.usi.inf.l3.ascala.atomic"))
    annList.find(p => p.symbol.tpe == atomicSymbol.tpe)
  }

  def aliasAnnotation(annList: List[AnnotationInfo]) = {
    val aliasSymbol = 
      rootMirror.getClass(newTypeName("ch.usi.inf.l3.ascala.alias"))
    annList.find(p => p.symbol.tpe == aliasSymbol.tpe)
  }
  
  def unitforAnnotation(annList: List[AnnotationInfo]) = {
    val aliasSymbol = 
      rootMirror.getClass(newTypeName("ch.usi.inf.l3.ascala.unitfor"))
    annList.find(p => p.symbol.tpe == aliasSymbol.tpe)
  }

  /**
   * Might need this if I decide to use java annotataions.
   *
   * TODO find a way to get the string value without using toString
   * to make it nicer and get rid of the quotations.
   */
  def j_atomicSetName(anno: AnnotationInfo) =
    anno.javaArgs.head._2.toString()

  /**
   *
   */
  def atomicSetName(anno: AnnotationInfo) = anno.args.head match {
    case Apply(_, Literal(value) :: Nil) => value.stringValue
    case _ => throw new Exception("Error getting atomic set name.")
  }

  /**
   * TODO this looks horrible, beautify, consider getOrElse. I am also
   * inconsistent whether to test this condition here or by the caller.
   */
  def ownerClassSymbol(t: Tree) = {
    if (hasSymbol(t))
      t.symbol.owner match {
        case s: ClassSymbol => Some(s)
        case s: MethodSymbol if (s.isClassConstructor) => Some(s.owner)
        case _ => None
      }
    else None
  }

  /**
   * This is a hasSymbol function from another point of view, which is more
   * commonly used in this code, Having the NoSymbol symbol is interpreted
   * as not having a Symbol as well.
   */
  def hasSymbol(t: Tree) = t.symbol != null && t.symbol != NoSymbol

  private def findSymbol(name: Name, tpe: Type, paramSyms: List[Symbol]) = {
    val r = paramSyms.foldLeft(List[Symbol]())((c, r) =>
      if (r.name == name && r.tpe =:= tpe) r :: c else c)

    r match {
      case head :: Nil => Some(head)
      case _ => None
    }
  }

  /**
   * When creating a new tree by duplicating and modifying an existing one,
   * all symbols of child trees should be updated.
   */
  private def changeOwner(tree: Tree, oldOwner: Symbol, newOwner: Symbol) {
    var list: Map[Symbol, Symbol] = Map.empty
    tree.foreach {
      (x: Tree) =>
        {
          if (x.symbol != null &&
            x.symbol != NoSymbol &&
            x.symbol.owner == oldOwner) {
            x match {
              case ident: Ident => ident.symbol = list(ident.symbol)
              case _ =>
                val ts = x.symbol
                val ns = x.symbol.cloneSymbol(newOwner)
                x.symbol = ns
                list = list + (ts -> ns)
                changeOwner(x, ts, ns)
            }
          }
        }
    }
  }

  /**
   * When creating a new tree by duplicating and modifying an existing one,
   * all symbols of child trees should be updated. This is the method
   * parameters version.
   *
   */
  def changeOwner(tree: Tree, oldSymb: Symbol,
    paramSyms: List[Symbol]): Unit = {
    tree.foreach {
      (x: Tree) =>
        {
          if (x.symbol != null &&
            x.symbol != NoSymbol &&
            x.symbol.owner == oldSymb) {
            val ns = findSymbol(x.symbol.name, x.symbol.tpe, paramSyms)
            x.symbol = ns match {
              case Some(s) => s
              case None => x.symbol
            }
          }
        }
    }
  }

  /******************* Phase 1: check annotation targets ************************/

  /**
   * Check that each annotation is on the right target
   */
  private object CheckAnnotationTargets extends PluginComponent {

    val global: AtomicScala.this.global.type = AtomicScala.this.global

    /* This is the earliest stage possible, each class will have a symbol after
     * this stage
     */
    val runsAfter = List[String]("typer");
    override val runsRightAfter = Some("typer")

    val phaseName = "check-annotation-targets"
    def newPhase(_prev: Phase) = new TargetsPhase(_prev)

    class TargetsPhase(prev: Phase) extends StdPhase(prev) {
      println("Targets phase is runnig...")
      override def name = CheckAnnotationTargets.this.phaseName

      def apply(unit: CompilationUnit) {
        //TODO fill in the implementation after more important tasks are done.
        //        unit.error(tree.pos, "Not the right target")
      }
    }
  }

  /****************** Phase 2: create class-set map *****************************/
  /**
   * Find which classes have atomic sets, the next phase will add lock fields
   * based on this information.
   */
  private object ClassSetsMapping extends PluginComponent {

    val global: AtomicScala.this.global.type = AtomicScala.this.global

    val runsAfter = List[String]("check-annotation-targets");
    override val runsRightAfter = Some("check-annotation-targets")

    val phaseName = "class-sets-mapping"
    def newPhase(_prev: Phase) = new ClassSetsPhase(_prev)

    class ClassSetsPhase(prev: Phase) extends StdPhase(prev) {

      println("Class to sets mapping phase is runnig...")

      override def name = ClassSetsMapping.this.phaseName

      /**
       * If the passed tree is a ValDef, return it as such.
       */
      def valTree(t: Tree) =
        t match {
          case ft @ ValDef(_, _, _, _) => Some(ft)
          case _ => None
        }

      /**
       * This is Symbol to be compatible with what I get when I try to get
       * the class symbol while transformation. In practice this should always
       * be a class Symbol. The purpose is to relate classes to their atomic
       * sets.
       */
      def addClassSetMapping(cs: Symbol, s: String) {
        if (classSetsMap.contains(cs)) classSetsMap(cs) = s :: classSetsMap(cs)
        else classSetsMap(cs) = s :: Nil
      }

      /**
       *  TODO I think I am mixing type checking with other things here,
       *  thus extra checks to see if the target is valid, this is not needed
       *  will move them to the first type-checking phase.
       *
       *  If the tree is a ValDef tree which is a var (:|) and is contained
       *  in a class, and has an annotation @atomic(set_name), add to the
       *  class-sets map a mapping of the owner class and the set name.
       */
      def addMapping(t: Tree) {
        /*
        * Not all these need to be calculated beforehand, optimize if needed.
        */
        val vt = valTree(t)
        val oc = ownerClassSymbol(t)
        val annos = annotationList(t)

        /*
        * TODO there are neater ways to encode this logic, explore them
        */
        val atomicAnno =
          if (annos != None) atomicAnnotation(annos.get) else None
        val asName =
          if (atomicAnno != None) Some(atomicSetName(atomicAnno.get)) else None

        if (vt != None && vt.get.symbol.isVar &&
          hasSymbol(vt.get) &&
          oc != None && asName != None) {
          //          println("adding "+ oc.get + " " + asName.get)
          addClassSetMapping(oc.get, asName.get)
        }

      }

      def apply(unit: CompilationUnit) {
        unit.body.foreach(addMapping)
        classSetsMap.foreach(println)
      }
    }
  }

  /************************ Phase 3: add lock fields ****************************/

  /**
   * Creates lock objects that correspond to each atomic set declaration in
   * a class. Uses information collected during phase.
   *
   * @author Nosheen Zaza
   */
  private object AddLockFields extends PluginComponent
    with Transform
    with TypingTransformers
    with TreeDSL {

    val global: GlobalType = AtomicScala.this.global

    val runsAfter = List[String]("class-sets-mapping");
    override val runsRightAfter = Some("class-sets-mapping")
    val phaseName = "add-lock-fields"

    def newTransformer(unit: CompilationUnit) = new AddLocksTransformer(unit)

    class AddLocksTransformer(unit: CompilationUnit)
      extends TypingTransformer(unit) {

      println("Add lock fields is running...")

      /**
       * Given a list of constructors, it adds a new parameter of lock type
       * to each constructor and returns a list of new constructors
       */
      def getNewConstructor(old_construcor: DefDef, lockType: Type) = {
        // Notice how we ask the class Symbol to generate the new param 
        // symbol, NOT the method symbol!
        val lock_sym =
          old_construcor.symbol.owner.newValueParameter(
            newTermName(as_lock), old_construcor.symbol.pos.focus)
            .setInfo(lockType)
            .setFlag(PARAM | PARAMACCESSOR | SYNTHETIC)

        val param = ValDef(lock_sym).setType(lockType)
        val newparamss = param :: old_construcor.vparamss.head
        val pList = newparamss :: old_construcor.vparamss.drop(1)

        val methDef = treeCopy.DefDef(
          old_construcor, old_construcor.mods, old_construcor.name,
          old_construcor.tparams,
          pList, old_construcor.tpt, old_construcor.rhs)

        methDef.symbol.owner.info.decls.unlink(methDef.symbol)

        val methodInfo = methDef.symbol.info.asInstanceOf[MethodType]

        methDef.symbol.updateInfo(MethodType(
          lock_sym :: methodInfo.params, methodInfo.resultType))

        // The field was not linked properly until this was added
        // this was inspired from:
        // Typers.scala line 1529
        // It is crazy that now I comment those and it still works!
        // talk about mind fuck.
        //        localTyper.namer.enterValueParams(
        //            List(List(param)) map (_.map(_.duplicate)))

        methDef.symbol.owner.info.decls.enter(lock_sym)
        methDef.symbol.owner.info.decls.enter(methDef.symbol)

        methDef
      }

      override def transform(tree: Tree): Tree = {
        tree match {
          case constructor: DefDef if (hasSymbol(constructor) &&
            constructor.symbol.isConstructor &&
            !constructor.symbol.owner.isModule &&
            classSetsMap.contains(constructor.symbol.owner)) =>

            val newC =
              getNewConstructor(constructor, getLockSym(lockClass).tpe)
            super.transform(newC)

          case _ => super.transform(tree)
        }
      }
    }
  }

  /********************** Phase 4: add synchronization ************************/
  /**
   * add synchronization blocks to each top-level public method in a class
   * that has one or more atomic sets.
   *
   * TODO currently no lock ordering or support for more than one atomic set.
   * @author Nosheen Zaza
   */
  private object AddSync extends PluginComponent
    with Transform
    with TypingTransformers
    with TreeDSL {

    val global: GlobalType = AtomicScala.this.global

    val runsAfter = List[String]("add-lock-fields");
    override val runsRightAfter = Some("add-lock-fields")
    val phaseName = "add-sync"

    def newTransformer(unit: CompilationUnit) = new AddSyncTransformer(unit)

    class AddSyncTransformer(unit: CompilationUnit)
      extends TypingTransformer(unit) {

      println("Add sync is running...")

      /**
       * Returns a new version of the arg class that contains the arg
       * method.
       *
       * pre: Passed class should NOT be a module or interface (for now)
       */
      def addMethodToClass(mt: DefDef, cl: ClassDef) = {
        localTyper.typed {
          treeCopy.ClassDef(cl, cl.mods,
            cl.symbol.name, cl.tparams,
            treeCopy.Template(cl.impl,
              cl.impl.parents,
              cl.impl.self,
              mt :: cl.impl.body))
        }.asInstanceOf[ClassDef]
      }

      def paramsWithUnitForSyms(md: DefDef) = {
        val mParamsSyms = md.vparamss.flatten.map(_.symbol)
        mParamsSyms.foldLeft(List[Symbol]())(
          (c, r) =>
            {
              val annos = r.annotations
              val uforAnno = 
                if (!annos.isEmpty) unitforAnnotation(annos) else None
              if (uforAnno != None) r :: c else c
            })
      }

      /**
       * Given another rhs implementation and a new name, returns a new
       * method ready to be plugged into the same class containing the original
       * prototype method.
       *
       * mt: Original method to be used as a prototype
       * nb: new rhs (body)
       * nName: the new Name
       */
      def getMethodWithNewBody(mt: DefDef, nb: Tree, nName: String) = {
        //TODO add the synch thing once you're sure this works
        val nbody = nb
        val tmargs = mt.vparamss.flatten //TODO remove the flatten later 
        val encClassSym = mt.symbol.enclClass

        val newMethodSym = encClassSym.newMethodSymbol(
          newTermName(nName),
          encClassSym.pos.focus,
          mt.symbol.flags)

        val paramSyms = map2(tmargs.map(_.symbol.tpe), tmargs.map(_.symbol)) {
          (tp, param) => newMethodSym.newSyntheticValueParam(tp, param.name)
        }

        val newMethodTpe = MethodType(paramSyms, mt.tpt.tpe)

        val newMethodparams = for ((p, s) <- (tmargs zip paramSyms)) yield {
          s.setInfo(p.symbol.tpe)
          ValDef(s, p.tpt)
        }

        if (encClassSym.info.decls.lookup(newMethodSym.name) == NoSymbol) {
          newMethodSym setInfoAndEnter newMethodTpe
        } else {
          newMethodSym setInfo newMethodTpe
        }

        changeOwner(nbody, mt.symbol, paramSyms)

        changeOwner(nbody, mt.symbol, newMethodSym)

        val tbody = localTyper.typedPos(newMethodSym.pos)(nbody)

        val methDef = DefDef(newMethodSym, List(newMethodparams), tbody)

        methDef.tpt setType localTyper.packedType(tbody, newMethodSym)

        localTyper.typed { (methDef).asInstanceOf[DefDef] }
      }
      
      def paramLocks(mt: DefDef) = {
        val p_ufor =  paramsWithUnitForSyms(mt)
        p_ufor.map(x => Select(Ident(x), newTermName(as_lock)))
      }
      
      def composeSync(locksList_sym: Symbol, n_locks: Int, tpt: Tree, body: Tree): Tree = {
          if (n_locks > 0) {
            val listApplyInt = 
              Select(Ident(locksList_sym), newTermName("apply"))
            val applyCall = Apply(listApplyInt, List(Literal(Constant(n_locks - 1))))
          
            val syncStmt =
              Apply(
                TypeApply(
                  Select(applyCall, newTermName("synchronized")),
                  List(tpt)),
                List(body))
                
            composeSync(locksList_sym, n_locks - 1, tpt, syncStmt)
          } else {
            println("BODY START")
            println(body)
            println("BODY END")
            body
          }
        }

      /**
       * given a method, takes the body and surrounds it with a synch block on
       * the lock object of the enclosing class.
       *
       * TODO think what to do when the method body is already synced on another
       * lock object. Probably the same should be done as a normal method but
       * ask Nate
       */
      def addSyncBLock(mt: DefDef) = {
        val mthdEncClass = mt.symbol.owner
        val lockModuleSym = getLockSym(lockClass).companionModule
        
        /*it is VERY important to type the tree right here because we are 
         * using its type to construct a type tree an the enclosing tree.
         * It does not work to type the overall tree later.
         * */
        val classLockField = localTyper.typed(Select(This(mthdEncClass), newTermName(as_lock)))
        
        // The call to Apply method of a List used to create a new list
        val listApply = 
          (TypeApply(Select(Ident(definitions.ListModule), 
              newTermName("apply")), List(TypeTree(classLockField.tpe))))
        
        val p_locks = paramLocks(mt)
        val all_locks = classLockField :: p_locks
        val lockList = Apply(listApply, all_locks) 
        
        /* the compiler is smarter than I thought. It found the method and the
         * local typer bound it correctly! */
        val sortedLockList = 
          localTyper.typed(Select(lockList, newTermName("sorted")))     
        
        val locksList_sym = mt.symbol.newValue(
            mt.rhs.pos.focus, newTermName("locks")).setInfo(sortedLockList.tpe)
        val locksList = ValDef(locksList_sym, sortedLockList)

        // It seems that calling duplicate is needed, otherwise I get an
        // exception.
        val nestedSync = 
          composeSync(locksList_sym, all_locks.size, 
              mt.tpt.duplicate , mt.rhs.duplicate)
        
        val blockToInsert = Block(locksList, nestedSync)
        blockToInsert
      }

      override def transform(tree: Tree): Tree = {
        def passNewLock(oldArgs: List[Tree], ownerClassTpt: Tree) = {
          /*
           * TODO create a special phase for this work here.
           * 
           * Remember that the modified constructor type are available and so
           * there is no need to change the associated symbol here, to prove
           * that to yourself: println(newStmt.symbol.infosString)
           * 
           * Also, arguements do not have symbols. No need to create a symbol
           * for the new argument. 
           * 
           * The newArg can be introduced like this too: 
           * val lockModuleSym = getLockSym(lockClass).companionModule
           * val newArg = Apply(
           *   Select(Ident(lockModuleSym), newTermName("apply")), Nil)
           */

          val newArg = reify { ch.usi.inf.l3.as.plugin.OrderedLock(); }.tree
          val newArgs = newArg :: oldArgs
          val newStmtM =
            localTyper.typed(
              Apply(Select(New(ownerClassTpt), nme.CONSTRUCTOR), newArgs))
          newStmtM
        }

        tree match {
          case cl: ClassDef =>
            val newClass = localTyper.typed {
              treeCopy.ClassDef(cl, cl.mods,
                cl.symbol.name, cl.tparams,
                treeCopy.Template(cl.impl,
                  cl.impl.parents,
                  cl.impl.self,
                  cl.impl.body.foldLeft(cl.impl.body)((c, r) =>
                    methodTransform(r) match {
                      case nm @ Some(_) => nm.get :: c
                      case None => c
                    })))
            }.asInstanceOf[ClassDef]
            super.transform(newClass)

          case valNewRHS @ ValDef(mods, name, tpt,
            Apply(Select(New(ntpt), nme.CONSTRUCTOR), args)) if (classSetsMap.contains(ntpt.symbol)) =>

            val annos = annotationList(valNewRHS)
            val aliasA = if (annos != None) aliasAnnotation(annos.get) else None
            aliasA match {
              case Some(_) =>
                val ownerClass = valNewRHS.symbol.enclClass
                val lock_f = ownerClass.info.findMember(newTermName(as_lock), 0, 0, false)

                if (lock_f == NoSymbol || lock_f == null)
                  throw new Exception("Enclosing class does not have atomic sets")
                val newArg = Select(This(ownerClass), newTermName(as_lock))

                val newArgs = newArg :: args

                val newRHS = localTyper.typed(
                  Apply(Select(New(ntpt), nme.CONSTRUCTOR), newArgs))
                val newvalDef = treeCopy.ValDef(valNewRHS, mods, name, tpt, newRHS)
                super.transform(localTyper.typed(newRHS))

              case None =>
                val newRHS = passNewLock(args, ntpt)
                val newvalDef = treeCopy.ValDef(valNewRHS, mods, name, tpt, newRHS)
                super.transform(localTyper.typed(newRHS))
            }

//          case vDef @ ValDef(_, _, _, _)  =>
//            println(showRaw(vDef))
//            super.transform(tree)
            
          case _ => super.transform(tree)
        }
      }

      def methodTransform(tree: Tree) = {
        //TODO think what other kinds of methods need not be synced
        tree match {
          case md: DefDef if hasSymbol(md) &&
            md.symbol.isMethod &&
            !md.symbol.isConstructor &&
            md.mods.isPublic &&
            classSetsMap.contains(md.symbol.owner) &&
            !md.symbol.isSynthetic &&
            !md.symbol.isGetter &&
            (md.symbol.name.toString() == "doSomething")
            =>
              println("NAME OF METHOD: " + md.symbol.name)
            Some(getMethodWithNewBody(
              md, addSyncBLock(md), md.name + "__w_lock"))
          case _ => None
        }
      }
    }
  }
}