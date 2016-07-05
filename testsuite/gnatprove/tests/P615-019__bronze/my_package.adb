package body My_Package with SPARK_Mode is

   procedure Search (A      : Nat_Array;
                     E      : Natural;
                     Found  : out Boolean;
                     Result : out Positive)
   is
   begin
      for I in A'Range loop
         if A (I) = E then
            Found := True;
            Result := I;
            return;
         end if;
      end loop;
      Found := False;
   end Search;

   procedure Test is
      A : Nat_Array (1 .. 3);
   begin
      A (1) := 1;
      pragma Annotate
        (GNATprove, False_Positive, """A"" might not be initialized",
         String'("A is properly initialized by these three successive"
           & " assignments"));
      A (2) := 2;
      A (3) := 3;
   end Test;

   procedure Do_Not_Modify_X (X, Y : in out Integer) is
   begin
      Y := Y + X;
   end Do_Not_Modify_X;

   procedure Write_X_Twice (X : out Integer) is
   begin
      X := 1;
      X := 2;
   end Write_X_Twice;

   procedure Write_X_To_Same (X : in out Integer) is
      Y : Integer;
   begin
      Y := X;
      X := Y;
   end Write_X_To_Same;

   function Init_Result_Twice return Integer is
      Result : Integer := 0;
   begin
      Result := 1;
      return Result;
   end Init_Result_Twice;

   procedure Set_To_One (X : out Integer) with Pre => True is
   begin
      X := 1;
   end Set_To_One;

   procedure Initialize_X (X : out Integer) is
      Y : Integer;
   begin
      Set_To_One (Y);
      X := 1;
   end Initialize_X;

   procedure Initialize_X2 (X : in out Integer) is
   begin
      X := 1;
   end Initialize_X2;

   procedure Do_Nothing is
   begin
      null;
   end Do_Nothing;

   X : Integer := 0;

   Y : Integer := 0;

   procedure Set_X_To_Y (X : out Integer) with
     Global => (Input => Y)
   is
      C : constant Integer := Y;
      procedure Set_X_To_C with
        Global => (Input => C, Output => X)
      is
      begin
         X := C;
      end Set_X_To_C;
   begin
      Set_X_To_C;
   end Set_X_To_Y;

   package P with Abstract_State => State is
      V : Integer;  --  V is visible in P so cannot be part of State

      procedure Update_All with
        Global => (Output => (V, State));
   private
      H : Integer with  --  H is hidden in P, it must be part of State
        Part_Of => State;
   end P;

   package body P with Refined_State => (State => (H, B)) is
      B : Integer; --  B is hidden in P, it must be part of State

      procedure Update_All is
      begin
         V := 0;
         H := 0;
         B := 0;
      end Update_All;
   end P;

   package P2 with
   Abstract_State => (State1, State2)
   is
      procedure Update_Only_H with
        Global => (Output => (State1));
      --  If only one abstract state was defined for B and H, the Global
      --  contract would be less precise.

   private
      H : Integer with
        Part_Of => State1;
   end P2;

   package body P2 with
   Refined_State => (State1 => H, State2 => B)
   is
      B : Integer := 0; --  B is hidden in P, it must be part of State

      procedure Update_Only_H is
      begin
         H := 0;
      end Update_Only_H;
   end P2;

   procedure Swap_With_Y (X : in out Integer) with Pre => True is
      Tmp : constant Integer := X;
   begin
      X := Y;
      Y := Tmp;
   end Swap_With_Y;

   procedure Swap (X, Y : in out Integer) with Pre => True is
      Tmp : constant Integer := X;
   begin
      X := Y;
      Y := Tmp;
   end Swap;

   type T is record
      F1 : Integer;
      F2 : Integer;
   end record with Convention => C_Pass_By_Copy;

   XX : T := (others => 0);

   YY : T := (others => 0);

   procedure Move_X_To_Y (X : in T; Y : out T) with Pre => True is
   begin
      Y := X;
   end Move_X_To_Y;

   procedure Move_X_To_Y1 (X : in T) with Pre => True is
   begin
      YY := X;
   end Move_X_To_Y1;

   procedure Move_X_To_Y2 (Y : out T) with Pre => True is
   begin
      Y := XX;
   end Move_X_To_Y2;

   procedure Move_X_To_Y (X : in Integer; Y : out Integer) with Pre => True is
   begin
      Y := X;
   end Move_X_To_Y;

   procedure Move_X_To_Y1 (X : in Integer) with Pre => True is
   begin
      Y := X;
   end Move_X_To_Y1;


   procedure Move_X_To_Y2 (Y : out Integer) with Pre => True is
   begin
      Y := X;
   end Move_X_To_Y2;

   procedure Only_Read_F2_Of_X (Y : out Integer) with Pre => True is
   begin
      Y := XX.F2;
   end Only_Read_F2_Of_X;

   procedure Bad_Aliasing is
      Z : T := (others => 0);
      A : Nat_Array (1 .. 2) := (others => 0);
      I : Integer := 2;
   begin
      Swap_With_Y (Y);
      --  Swap (Y, Y);
      Move_X_To_Y (Z, Z);
      Move_X_To_Y (Y, Y);
      Move_X_To_Y1 (Y);
      Move_X_To_Y2 (XX);
      Move_X_To_Y2 (X);

      Move_X_To_Y1 (YY);
      pragma Annotate
        (GNATprove, False_Positive,
         "formal parameter ""X"" and global ""YY"" are aliased",
         String'("My compiler follows Ada RM-B-3 68 implementation advice"
           & " and passes T by copy as it has the C_Pass_By_Copy convention"));

      Only_Read_F2_Of_X (XX.F1);
      pragma Annotate
        (GNATprove, False_Positive,
         "formal parameter ""Y"" and global ""XX"" are aliased",
         String'("Only_Read_F2_Of_X only references the field F2 in X"
           & " so no aliasing can be introduced with X.F1"));

      pragma Assert (I = 2);
      Swap (A (1), A (I));
      pragma Annotate
        (GNATprove, False_Positive,
         "formal parameters ""X"" and ""Y"" might be aliased",
         String'("As I is equal to 2 prior to the call, A (1) and A (I) are"
           & " never aliased."));
   end Bad_Aliasing;

end My_Package;
