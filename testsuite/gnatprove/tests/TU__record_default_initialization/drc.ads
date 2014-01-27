package DRC
  with SPARK_Mode => On
is

   -- TU: 1. If at least one non-discriminant component (either explicitly
   --     declared or inherited) of a record type or type extension either is
   --     of a type which defines full default initialization or is declared
   --     by a ``component_declaration`` which includes a
   --     ``default_expression``, and if that component's type has at least
   --     one elementary non-discriminant part, then the record type or type
   --     extension shall define full default initialization.

   -- Below, "DI" = "Default Initialization"
   --
   -- See also the definition of Full DI in RM 3.1.


   type R1 is record -- No DI, legal
      F1 : Integer;
      F2 : Integer;
   end record;

   type R2 is record -- Full DI, legal
      F1 : Integer := 0;
      F2 : Integer := 1;
   end record;

   type R3 is record -- partial DI, illegal
      F1 : Integer := 0;
      F2 : Integer;
   end record;

   type R4 is record -- partial DI, illegal
      F1 : Integer;
      F2 : Integer := 1;
   end record;

   type R5 is record -- partial DI, illegal
      F1 : R1;              -- no FDI, therefore
      F2 : Boolean := True; -- this is illegal
   end record;

   type R6 is record -- No DI, legal
      F1 : R1;
      F2 : Boolean;
   end record;

   type R7 is record -- Partial DI, nested records
      F1 : R2;       -- DI, therefore
      F2 : Boolean;  -- this is illegal
   end record;

   type R8 is record -- Full DI, nested records
      F1 : R2;               -- DI, therefore
      F2 : Boolean := False; -- this is legal
   end record;

   -- Tests involving scalar user-defined type that
   -- has a default value
   type TDI is range 0 .. 10
     with Default_Value => 0;

   type R9 is record -- one field, DI, so OK
      F1 : TDI;
   end record;

   type R10 is record -- two fields, both DI, so OK
      F1 : TDI;
      F2 : Integer := 1;
   end record;

   type R11 is record -- two fields, partial DI, so illegal
      F1 : TDI;
      F2 : Integer;
   end record;

   -- Tests involving array with default component value
   type A is array (TDI) of Integer
     with Default_Component_Value => 0;

   type R12 is record -- one field, DI, so OK
      F1 : A;
   end record;

   type R13 is record -- two fields, both DI, so OK
      F1 : A;
      F2 : Integer := 1;
   end record;

   type R14 is record -- two fields, partial DI, so illegal
      F1 : A;
      F2 : Integer;
   end record;

   -- Tests involving array with element type that has DI
   type A2 is array (Boolean) of TDI;

   type R15 is record -- one field, DI, so OK
      F1 : A2;
   end record;

   type R16 is record -- two fields, both DI, so OK
      F1 : A2;
      F2 : Integer := 1;
   end record;

   type R17 is record -- two fields, partial DI, so illegal
      F1 : A2;
      F2 : Integer;
   end record;

   -- Type derivation
   type R18 is new R16; -- legal
   type R19 is new R17;

   -- Type extension
   --
   -- Currently not possible to test, since is only
   -- legal with tagged types, which are not supported
   -- in rel 1 of SPARK 2014.

end DRC;
