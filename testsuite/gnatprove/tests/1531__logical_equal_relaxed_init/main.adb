procedure Main with SPARK_Mode is
   type Rec is record
      A, B : Integer;
   end record;

   function Eq (X, Y : Rec) return Boolean with
     Ghost, Import, Global => null,
     Relaxed_Initialization => (X, Y),
     Annotate => (GNATprove, Logical_Equal);

   procedure Record_Call (X, Y : Rec) with
     Ghost, Global => null,
     Relaxed_Initialization => (X, Y);

   procedure Record_Call (X, Y : Rec) is
      Result : constant Boolean := Eq (X, Y);
      Initialized : constant Rec := (1, 2);
      Mixed : constant Boolean := Eq (X, Initialized);
   begin
      pragma Assert (Result = Eq (X, Y));
      pragma Assert (Mixed = Eq (X, Initialized));
      if Eq (X, Y) then
         pragma Assert (Eq (X, Y));
      else
         pragma Assert (not Eq (X, Y));
      end if;
   end Record_Call;

   procedure Record_Initialization (X, Y : Rec) with
     Ghost, Global => null,
     Relaxed_Initialization => (X, Y),
     Pre => Eq (X, Y),
     Post => X.A'Initialized = Y.A'Initialized
       and then X.B'Initialized = Y.B'Initialized;

   procedure Record_Initialization (X, Y : Rec) is null;

   type Relaxed_Rec is record
      F : Integer;
   end record with Relaxed_Initialization;

   function Eq (X, Y : Relaxed_Rec) return Boolean with
     Ghost, Import, Global => null,
     Relaxed_Initialization => X,
     Annotate => (GNATprove, Logical_Equal);

   procedure Type_Relaxation (X, Y : Relaxed_Rec) with
     Ghost, Global => null,
     Pre => Eq (X, Y),
     Post => X.F'Initialized = Y.F'Initialized;

   procedure Type_Relaxation (X, Y : Relaxed_Rec) is null;

   type Int_Array is array (Positive range <>) of Integer;

   function Eq (X, Y : Int_Array) return Boolean with
     Ghost, Import, Global => null,
     Relaxed_Initialization => (X, Y),
     Annotate => (GNATprove, Logical_Equal);

   procedure Array_Call (X, Y : Int_Array) with
     Ghost, Global => null,
     Relaxed_Initialization => (X, Y);

   procedure Array_Call (X, Y : Int_Array) is
      Result : constant Boolean := Eq (X, Y);
   begin
      pragma Assert (Result = Eq (X, Y));
   end Array_Call;

   procedure Array_Initialization (X, Y : Int_Array) with
     Ghost, Global => null,
     Relaxed_Initialization => (X, Y),
     Pre => Eq (X, Y),
     Post => X'Initialized = Y'Initialized;

   procedure Array_Initialization (X, Y : Int_Array) is null;

   type Int_Matrix is array (Positive range <>, Positive range <>) of Integer;

   function Eq (X, Y : Int_Matrix) return Boolean with
     Ghost, Import, Global => null,
     Relaxed_Initialization => (X, Y),
     Annotate => (GNATprove, Logical_Equal);

   procedure Matrix_Call (X, Y : Int_Matrix) with
     Ghost, Global => null,
     Relaxed_Initialization => (X, Y);

   procedure Matrix_Call (X, Y : Int_Matrix) is
      Result : constant Boolean := Eq (X, Y);
   begin
      pragma Assert (Result = Eq (X, Y));
   end Matrix_Call;

   procedure Matrix_Initialization (X, Y : Int_Matrix) with
     Ghost, Global => null,
     Relaxed_Initialization => (X, Y),
     Pre => Eq (X, Y),
     Post => X'Initialized = Y'Initialized;

   procedure Matrix_Initialization (X, Y : Int_Matrix) is null;

   type Boolean_Rec is record
      Flag : Boolean;
   end record;

   function Eq (X, Y : Boolean_Rec) return Boolean with
     Ghost, Import, Global => null,
     Relaxed_Initialization => (X, Y),
     Annotate => (GNATprove, Logical_Equal);

   function Wrapped_Eq (X, Y : Boolean_Rec) return Boolean is (Eq (X, Y)) with
     Ghost, Relaxed_Initialization => (X, Y);

   procedure Check_Condition (X : Boolean_Rec) with
     Ghost, Global => null,
     Relaxed_Initialization => X,
     Pre => not X.Flag'Initialized;

   procedure Check_Condition (X : Boolean_Rec) is
      F : constant Boolean_Rec := (Flag => False);
      T : constant Boolean_Rec := (Flag => True);
   begin
      --  Neither initialized record is logically equal to X

      if Wrapped_Eq (X, F) then
         null;
      elsif Wrapped_Eq (X, T) then
         null;
      else
         pragma Assert (False); -- @ASSERT:FAIL
      end if;
   end Check_Condition;
begin
   null;
end Main;
