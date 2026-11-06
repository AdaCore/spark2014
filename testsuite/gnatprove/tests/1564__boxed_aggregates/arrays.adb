procedure Arrays with SPARK_Mode is
   type I is new Integer with Relaxed_Initialization;
   type A is array (1 .. 2) of I;

   procedure Relaxed_Elements (Result : out I) with Global => null is
      X : A := (others => <>);
   begin
      Result := X (1); -- @INIT_BY_PROOF:FAIL
   end Relaxed_Elements;

   procedure Evaluated_Element (Result : out I) with Global => null is
      Value : I;
      X : A := (1 => Value, others => <>); -- @INIT_BY_PROOF:FAIL
   begin
      Result := X (1); -- @INIT_BY_PROOF:PASS
      pragma Assert (X (2)'Initialized); -- @ASSERT:FAIL
   end Evaluated_Element;

   type Relaxed_Array is array (1 .. 2) of Integer
     with Relaxed_Initialization;

   procedure Enclosing_Relaxation (Result : out Integer) with Global => null is
      X : Relaxed_Array := (others => <>);
   begin
      Result := X (1); -- @INIT_BY_PROOF:FAIL
   end Enclosing_Relaxation;

   type Matrix is array (1 .. 2, 1 .. 2) of Integer
     with Relaxed_Initialization;

   procedure Multidimensional (Result : out Integer) with Global => null is
      X : Matrix := (others => (others => <>));
   begin
      Result := X (1, 1); -- @INIT_BY_PROOF:FAIL
   end Multidimensional;

   type R is record
      F : Integer;
      G : Integer := 42;
   end record;
   type Record_Array is array (1 .. 2) of R
     with Relaxed_Initialization;

   procedure Composite_Elements (Result : out Integer) with Global => null is
      X : Record_Array := (others => <>);
   begin
      pragma Assert (X (1).G = 42);
      Result := X (1).F; -- @INIT_BY_PROOF:FAIL
   end Composite_Elements;

   type Defaulted_Array is array (1 .. 2) of Integer with
     Default_Component_Value => 42, Relaxed_Initialization;

   procedure Default_Component (Result : out Integer) with Global => null is
      X : Defaulted_Array := (others => <>);
   begin
      Result := X (1); -- @INIT_BY_PROOF:PASS
      pragma Assert (Result = 42);
   end Default_Component;

   type Defaulted_I is new Integer with
     Default_Value => 42, Relaxed_Initialization;
   type Defaulted_Elements is array (1 .. 2) of Defaulted_I;

   procedure Default_Value (Result : out Defaulted_I) with Global => null is
      X : Defaulted_Elements := (others => <>);
   begin
      Result := X (1); -- @INIT_BY_PROOF:PASS
      pragma Assert (Result = 42);
   end Default_Value;

   type Plain_Defaulted_I is new Integer with Default_Value => 42;
   type Enclosing_Default is array (1 .. 2) of Plain_Defaulted_I
     with Relaxed_Initialization;

   procedure Default_Element_Type (Result : out Plain_Defaulted_I) with
     Global => null
   is
      X : Enclosing_Default := (others => <>); -- @INIT_BY_PROOF:NONE
   begin
      Result := X (1); -- @INIT_BY_PROOF:PASS
      pragma Assert (Result = 42);
   end Default_Element_Type;

   type Plain_Array is array (1 .. 2) of Plain_Defaulted_I;

   procedure Ordinary_Default (Result : out Plain_Defaulted_I) with
     Global => null
   is
      X : Plain_Array := (others => <>); -- @INIT_BY_PROOF:NONE
   begin
      Result := X (1);
      pragma Assert (Result = 42);
   end Ordinary_Default;
begin
   null;
end Arrays;
