-- MB27-015 - legality of variables in expressions.
--
-- This test case shows examples of both legal and illegal
-- use of variables inside renamings of function calls.
--
-- See SPARK LRM 4.4(2) fifth bullet.
package Q is

   -- TU: 2. An expression (or range) in |SPARK| occurring in certain contexts
   --  (listed below) shall not have a variable input. This means that
   --  such an expression shall not read a variable, nor shall it call a
   --  function which (directly or indirectly) reads a variable. These
   --  contexts include:
   --   * a constraint excluding the range of a loop parameter
   --     specification where variables may be used in the expressions
   --     defining the range (see :ref:`subtype_declarations`);
   --   * the default_expression of a component declaration (see
   --     :ref:`record_types`);
   --   * the default_expression of a discriminant_specification
   --     (see :ref:`discriminants`);
   --   * a Dynamic_Predicate or Type_Invariant aspect specification;
   --   * an indexing expresssion of an indexed_component or the discrete_range
   --     of a slice in an object renaming declaration which renames
   --     part of that index or slice;
   --   * a generic actual parameter corresponding to a generic formal
   --     object having mode **in**.

   type T is range 1 .. 10;

   type Arr is array (T) of Boolean;

   Null_Arr : constant Arr := Arr'(others => False);

   Arr_Obj : Arr := Null_Arr;

   V : T := 1;

   function Get_V return T
     with Global => V;

   function Get_P (I : in T) return T;

   function Get_Arr return Arr
     with Global => Arr_Obj;

   function Get_Arr_P1 (X : in Arr) return Arr;

   function Get_Arr_P2 (X : in Arr; I : in T) return Boolean;

end Q;
