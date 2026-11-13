procedure Test_Relaxed_Traversal with SPARK_Mode is

   type Int_Access is access Integer;
   type Holder is record
      Value : Int_Access;
   end record with Relaxed_Initialization;

   procedure Test_Record (X : in out Holder) with
     Pre => X.Value'Initialized and then X.Value /= null;

   procedure Test_Record (X : in out Holder) is
      function Reference (X : in out Holder) return not null access Integer
      is (X.Value)
      with Pre => X.Value'Initialized and then X.Value /= null;
   begin
      declare
         Y : constant not null access Integer := Reference (X);
      begin
         Y.all := 42;
      end;
      pragma Assert (X.Value'Initialized);
      pragma Assert (X.Value.all = 42);
   end Test_Record;

   type Element is record
      Value : Integer;
   end record with Relaxed_Initialization;
   type Arr is array (Positive range <>) of aliased Element;

   procedure Test_Array is
      function Reference (X : aliased in out Arr) return not null access Arr
      is (X'Access);

      function First (X : aliased in out Arr) return not null access Element
      is (X (X'First)'Access)
      with Pre => X'Length > 0;

      X : aliased Arr := (1 .. 2 => <>);
   begin
      declare
         Y : constant not null access Arr := Reference (X);
      begin
         Y (1).Value := 42;
      end;
      pragma Assert (X (1).Value'Initialized);
      pragma Assert (X (1).Value = 42);
      declare
         Y : constant not null access Element := First (X);
      begin
         Y.Value := 43;
      end;
      pragma Assert (X (1).Value'Initialized);
      pragma Assert (X (1).Value = 43);
   end Test_Array;

   type Plain_Array is array (Positive range <>) of aliased Integer;

   procedure Test_Parameter is
      function First
        (X : aliased in out Plain_Array) return not null access Integer
      is (X (X'First)'Access)
      with Relaxed_Initialization => X,
        Pre => X'Length > 0 and then X (X'First)'Initialized;

      X : aliased Plain_Array := (1 .. 2 => 0);
   begin
      declare
         Y : constant not null access Integer := First (X);
      begin
         Y.all := 42;
      end;
      pragma Assert (X (1) = 42);
   end Test_Parameter;

begin
   Test_Array;
   Test_Parameter;
end Test_Relaxed_Traversal;
