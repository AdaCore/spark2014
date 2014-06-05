package Legality
  with SPARK_Mode => On
is
   -- Cases for the placement of Volatile_Components

   -- See RM C.6(6.5/3) which basically says that Volatile_Components
   -- can appear on an entity which is either
   --  1) a full type declaration of an array type
   -- or
   --  2) the implicit full type declaration associated with an
   --     array object of an anonymous type.
   -- Comments below refer to one of both of these cases by number

   type I is range 1 .. 10;

   type A0 is array (I) of Boolean; -- OK

   type A1 is array (I) of Boolean
     with Volatile_Components; -- OK 1

   type A1p is array (I) of Boolean;
     pragma Volatile_Components (A1p); -- OK 1

   type A2 is array (I) of Boolean
     with Volatile; -- OK

   type A3 is array (I) of Boolean
     with Volatile,
          Volatile_Components; -- OK 1

   VA00 : A0; -- OK
   VA01 : A0 with Volatile; -- OK
   VA02 : A0 with Volatile_Components; -- illegal 1
   VA03 : A0 with Volatile, Volatile_Components; -- illegal 1
   VA04 : A0 with Volatile_Components, Volatile; -- illegal 1

   VA10 : A1; -- OK
   VA11 : A1 with Volatile; -- OK
   VA12 : A1 with Volatile_Components; -- illegal 1
   VA13 : A1 with Volatile, Volatile_Components; -- illegal 1
   VA14 : A1 with Volatile_Components, Volatile; -- illegal 1

   VA20 : A2; -- OK
   VA21 : A2 with Volatile; -- OK
   VA22 : A2 with Volatile_Components; -- illegal 1
   VA23 : A2 with Volatile, Volatile_Components; -- illegal 1
   VA24 : A2 with Volatile_Components, Volatile; -- illegal 1

   VA30 : A3; -- OK
   VA31 : A3 with Volatile; -- OK
   VA32 : A3 with Volatile_Components; -- illegal 1
   VA33 : A3 with Volatile, Volatile_Components; -- illegal 1
   VA34 : A3 with Volatile_Components, Volatile; -- illegal 1

   -- Objects with anonymous array type
   AA0 : array (I) of Boolean; -- OK
   AA1 : array (I) of Boolean with Volatile; -- OK
   AA2 : array (I) of Boolean with Volatile_Components; -- OK 2
   AA3 : array (I) of Boolean with Volatile, Volatile_Components; -- OK 2
   AA4 : array (I) of Boolean with Volatile_Components, Volatile; -- OK 2

end Legality;
