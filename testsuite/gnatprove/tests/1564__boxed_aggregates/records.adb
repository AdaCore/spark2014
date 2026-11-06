procedure Records with SPARK_Mode is
   type R is record
      F : Integer;
      G : Integer := 42;
   end record with Relaxed_Initialization;

   procedure Boxed_Field (Result : out Integer) with Global => null is
      X : R := (F => <>, G => 1);
   begin
      Result := X.F; -- @INIT_BY_PROOF:FAIL
   end Boxed_Field;

   procedure Defaulted_Field (Result : out Integer) with Global => null is
      X : R := (F => 1, G => <>);
   begin
      Result := X.G; -- @INIT_BY_PROOF:PASS
      pragma Assert (Result = 42);
   end Defaulted_Field;

   type Inner is record
      F : Integer;
   end record;
   type Outer is record
      C : Inner;
   end record with Relaxed_Initialization;

   procedure Nested_Aggregate (Result : out Integer) with Global => null is
      X : Outer := (C => (F => <>));
   begin
      Result := X.C.F; -- @INIT_BY_PROOF:FAIL
   end Nested_Aggregate;

   procedure Composite_Default (Result : out Integer) with Global => null is
      X : Outer := (C => <>);
   begin
      Result := X.C.F; -- @INIT_BY_PROOF:FAIL
   end Composite_Default;

   type Defaulted is record
      F : Integer := 42;
   end record;
   type Holder is record
      C : Defaulted;
   end record with Relaxed_Initialization;

   procedure Full_Default (Result : out Integer) with Global => null is
      X : Holder := (C => <>); -- @INIT_BY_PROOF:NONE
   begin
      Result := X.C.F; -- @INIT_BY_PROOF:PASS
      pragma Assert (Result = 42);
   end Full_Default;

   type Empty is null record;
   type With_Empty is record
      C : Empty;
      F : Integer;
   end record with Relaxed_Initialization;

   procedure Empty_Component (Result : out Integer) with Global => null is
      X : With_Empty := (C => <>, F => 42); -- @INIT_BY_PROOF:NONE
   begin
      Result := X.F; -- @INIT_BY_PROOF:PASS
      pragma Assert (Result = 42);
   end Empty_Component;

   function Boxed_Result return R with
     Global => null,
     Post => Boxed_Result'Result'Initialized -- @POSTCONDITION:FAIL
   is
   begin
      return (F => <>, G => 1);
   end Boxed_Result;

   function Initialized_Result return R with
     Global => null,
     Post => Initialized_Result'Result'Initialized -- @POSTCONDITION:PASS
   is
   begin
      return (F => 1, G => <>);
   end Initialized_Result;

   type Plain_Holder is record
      C : Defaulted;
   end record;

   procedure Ordinary_Default (Result : out Integer) with Global => null is
      X : Plain_Holder := (C => <>); -- @INIT_BY_PROOF:NONE
   begin
      Result := X.C.F;
      pragma Assert (Result = 42);
   end Ordinary_Default;
begin
   null;
end Records;
