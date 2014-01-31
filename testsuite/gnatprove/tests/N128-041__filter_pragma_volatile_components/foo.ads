package Foo
is
   type Array_T is array (1 .. 10) of Integer;
   pragma Volatile_Components (Array_T);

   type Array_T2 is array (1 .. 10) of Integer with Volatile_Components;

   type Array_T3 is array (1 .. 10) of Integer;


   -- Test that the warning can be suppressed
   pragma Warnings (Off, "pragma*not yet supported*");

   type Array_T4 is array (1 .. 10) of Integer;
   pragma Volatile_Components (Array_T4);

   type Array_T5 is array (1 .. 10) of Integer
     with Volatile_Components;

   pragma Warnings (On, "pragma*not yet supported*");

   -- Some body using Array_T to demonsrate flow-analysis
   -- and proof involving such a type.
   function Sum (A : in Array_T) return Integer
     with Global => null,
          Post   => Sum'Result <= 100; -- something obviously not provable

end Foo;


