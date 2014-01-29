package body Foo
is

   type Array_T is array (1 .. 10) of Integer;
   pragma Volatile_Components (Array_T);

   type Array_T2 is array (1 .. 10) of Integer with Volatile_Components;

   type Array_T3 is array (1 .. 10) of Integer;

end Foo;
