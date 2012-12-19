Program Structure and Compilation Issues
========================================

Data flow analysis, unlike compilation, does not follow Ada's separate
compilation model. For example, functions in |SPARK| must be side-effect free;
this rule is enforced as part of data flow analysis. Suppose that a function
calls a procedure which in turn calls another procedure, which in turn calls
yet another. In the absence of Global aspect specifications for the
procedures in question, it would be necessary to analyze the bodies
of all subprograms called in order to determine whether the function
is side-effect free.

Limited Package Views
---------------------

Any state abstractions declared within a given package are present in
the limited view of the package.

[This means that, for example, a Globals aspect specification for a
subprogram declared in a library unit package P1 could refer to a state
abstraction declared in a package P2 if P1 has a limited with of P2.]

For every variable object declared by an object_declaration occuring
immediately within the visible part of a given package, the limited
view of the package contains an *abstract view* of the object.

A name denoting the abstract view of a variable shall occur only

   * as a global_item in a Global aspect specification; or
   * as an input or output in a Depends aspect specification.

The abstract view of a volatile variable is volatile. 

.. note::
  (SB) No need to allow such a name in other contexts where a name denoting
  a state abstraction could be legal. In particular, in an
  Initializes aspect spec or in any of the various refinement
  aspect specifications. Initializes aspect specs do not refer to
  variables in other packages. Refinements occur in bodies and bodies
  don't need limited withs.

.. note::
  (SB) Is the rule about volatility needed? I think this is needed in
  order to prevent a function's Global specification from mentioning
  an abstract view of a volatile variable, but I'm not sure because
  I don't understand what prevents a function's Global specification
  from mentioning the "concrete" view of a volatile variable.
  This problem is briefly mentioned at the beginning of the peculiarly
  numbered subsection 7.2 (package bodies) of section 7.2.4
  (volatile variables).


  
