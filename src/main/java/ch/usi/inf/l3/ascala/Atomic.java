package ch.usi.inf.l3.ascala;

/**
 * The target of this annotation is a class field decleration (TODO only var?)
 * It indicates that the annotated field is a member of the atomic set
 * given as a parameter to the annotation.
 */
public @interface Atomic {
	String value();
}
