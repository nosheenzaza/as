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
    AddLockFields,
    AddSync)

  type GlobalType = this.global.type

  /**
   * TODO later for optimization, I will need to relate sets to fields and not
   * only as class.
   */
  val classSetsMap = Map[Symbol, List[String]]()
  
  
  
/******************************* Utilities ************************************/
  
  /**
   * This is a hasSymbol function from another point of view, which is more 
   * commonly used in this code, Having the NoSymbol symbol is interpreted 
   * as not having a Symbol as well.
   */
  def hasSymbol(t: Tree) = t.symbol != null && t.symbol != NoSymbol
  
  private def findSymbol(name: Name, tpe: Type, 
      paramSyms: List[Symbol]): Option[Symbol] = {
    
      val r = for (p <- paramSyms if (p.name == name && p.tpe =:= tpe)) 
        yield { p }
      
      r match {
        case head :: Nil => Some(head)
        case _ => None
      }
    }

  /**
   * When creating a new tree by duplicating and modifying an existing one,
   * all symbols of child trees should be updated.
   */
  private def changeOwner(tree: Tree, oldOwner: Symbol,
    newOwner: Symbol): Unit = {

    var list: Map[Symbol, Symbol] = Map.empty

    tree.foreach {
      (x: Tree) => {
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
        (x: Tree) => {
            if (x.symbol != null && 
                x.symbol != NoSymbol&& 
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
    val runsAfter = List[String]("refchecks");
    override val runsRightAfter = Some("refchecks")

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
            case s: MethodSymbol if(s.isClassConstructor) => Some(s.owner) 
            case _ => None
          }
        else None
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

        if (vt != None &&  vt.get.symbol.isVar &&  
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
   * TODO fill phase name.
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

      def getConstructors(klass: ClassDef) =
        klass.impl.body.
          filter(_.symbol.name == nme.CONSTRUCTOR).map(_.asInstanceOf[DefDef])
      
      def modifyConstructors(klass: ClassDef) = {
        val cnsts = getConstructors(klass)
        val newCnsts = cnsts.map {
          (x: DefDef) =>
            {
              val sym = x.symbol.newValueParameter(newTermName("lock"))
              sym.setInfo(definitions.ObjectTpe)
              
              val lock = ValDef(sym, Ident(definitions.ObjectClass))
              
              /* This statement is crazy, but it is needed due to the  scala 
               * compiler architecture. Although we have told the compiler 
               * to inherit all the information needed for the ValDef tree from 
               * the sym Symbol (including: name, type and everything else) 
               * the compiler forgets to inherit the tpe information!! So we 
               * had to inherit it manually.
               */ 
              lock.tpe = sym.info
              val newparamss = x.vparamss match {
                case Nil => List(List(lock))
                case x :: xs => (lock :: x) :: xs
              }
              localTyper.typed(treeCopy.DefDef(x, x.mods, x.name,
                  x.tparams, newparamss, x.tpt, x.rhs))
            }
        }

        val allButCnst = klass.impl.body.
          filter(_.symbol.name != nme.CONSTRUCTOR)

        val newImpl = treeCopy.Template(klass.impl, klass.impl.parents,
          klass.impl.self, newCnsts ++ allButCnst)

        localTyper.typed(
          treeCopy.ClassDef(klass, klass.mods,
            klass.name, klass.tparams, newImpl))
      }
      
      def modifyNewStmts(newStmt: Apply, args: List[Tree]) = {
        // create a new lock argument
        val newArg = reify{new Object()}
        
        // append it to the argument list
        val newArgList = newArg.tree :: args
        
        localTyper.typed(treeCopy.Apply(newStmt, newStmt.fun, newArgList))
      }
      
      override def transform(tree: Tree): Tree = {
        
        tree match {
          case klass @ ClassDef(_, _, _, _) =>
            // for now one atomic set per class, that is, we insert a 
            // single lock for any class that declares at least one atomic 
            // set. Should be easy to fix later.
            if(!klass.symbol.isModule && classSetsMap.contains(klass.symbol)) {
	            val newClass = modifyConstructors(klass)
	            super.transform(newClass)
            }
            else super.transform(tree)
            
          case newStmt @ Apply(Select(New(tpt), nme.CONSTRUCTOR), args) =>
            if(classSetsMap.contains(tpt.symbol)) {
//              println("modified to " + modifyNewStmts(newStmt, args))
              super.transform(modifyNewStmts(newStmt, args))
            } 
            else super.transform(tree)
            
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
        val obody = mt.rhs.duplicate
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
        
        changeOwner(obody, mt.symbol, paramSyms)
        
        changeOwner(obody, mt.symbol, newMethodSym)
        
        val tbody = localTyper.typedPos(newMethodSym.pos)(obody)

        val methDef = DefDef(newMethodSym, List(newMethodparams), tbody)
        
        println(" new method here: " )
                
        methDef.tpt setType localTyper.packedType(tbody, newMethodSym)
        
        localTyper.typed {(methDef).asInstanceOf[DefDef]}
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
       val mthdEncClass = mt.symbol.enclClass
       
       val mthdEncClassTName = mthdEncClass.name.toTypeName
       
       // TODO make sure this works
       // TODO it does not work when the return type is unit
       val synchBlock = 
         Apply(
           TypeApply(
               Select(Select(This(mthdEncClassTName), newTermName("lock")),
                 newTermName("synchronized")), 
               List(mt.tpt)), // maybe here duplication is needed
           List(mt.rhs)) // think this duplication is needed
        
       println(showRaw(mt))
       println("new synch" + synchBlock)
       synchBlock
      }
      override def transform(tree: Tree): Tree = {
        tree match {
          case cl: ClassDef =>     
            val newClass = localTyper.typed {
              treeCopy.ClassDef(cl, cl.mods,
                cl.symbol.name, cl.tparams,
                treeCopy.Template(cl.impl,
                  cl.impl.parents,
                  cl.impl.self,
                  cl.impl.body.foldLeft(cl.impl.body)((c, r) => 
                    methodTransform(r) match{
                      case nm @ Some(_) => nm.get :: c
                      case None => c
                    } )))
            }.asInstanceOf[ClassDef]
            println("new class: " + newClass)
            super.transform(newClass)
          case _ => super.transform(tree)
        }
        
      }
      
      def methodTransform(tree: Tree): Option[Tree] = {
        tree match {
          case md: DefDef 
          	if hasSymbol(md) &&  
          	   md.symbol.isMethod && 
          	   !md.symbol.isConstructor &&
          	   md.mods.isPublic &&
          	//TODO check the has owner thing
          	classSetsMap.contains(md.symbol.owner) &&
          	md.symbol.nameString == "foo" => 
          	  println("working on method "+ md.symbol.name)
          	  Some(getMethodWithNewBody(md, md.rhs, addSyncBLock(md) + "_w_lock"))
          case _ => None
        }
      }
    }
  }
}