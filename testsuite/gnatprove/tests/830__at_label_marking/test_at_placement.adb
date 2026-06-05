pragma Extensions_Allowed (All_Extensions);

procedure Test_At_Placement with SPARK_Mode
is

   --  References to At should not cross Assert_And_Cut pragmas

   procedure Assert_And_Cut_1 (X : in out Integer) is
      Y : Integer;
   begin
      X := X / 2;
      <<L1>>
      X := 15;
      pragma Assert_And_Cut (X = 15);
      Y := X'At (L1); --  Should be rejected, L1 is hidden by the assert and cut
   end Assert_And_Cut_1;

   procedure Assert_And_Cut_2 (X : in out Integer) is
      Y : Integer;
   begin
      X := X / 2;
      <<L1>>
      X := 15;
      pragma Assert_And_Cut (X = 15);
      if X = 12 then
         Y := X'At (L1); --  Should be rejected, L1 is hidden by the assert and cut
      end if;
   end Assert_And_Cut_2;

   procedure Assert_And_Cut_3 (X : in out Integer) is
      Y : Integer;
   begin
      X := X / 2;
      <<L1>>
      begin
         X := 15;
         pragma Assert_And_Cut (X = 15);
      end;
      if X = 12 then
         Y := X'At (L1); --  OK, L1 is not hidden by the assert and cut
      end if;
   end Assert_And_Cut_3;

   procedure Assert_And_Cut_4 (X : in out Integer) is
      Y : Integer;
   begin
      X := X / 2;
      pragma Assert_And_Cut (X > 0);
      <<L1>>
      X := 15;
      Y := X'At (L1); --  OK, L1 is not hidden by the assert and cut
   end Assert_And_Cut_4;

   procedure Assert_And_Cut_5 (X : in out Integer) is
      Y : Integer;
   begin
      X := X / 2;
      <<L1>>
      X := X + 1;
      pragma Assert_And_Cut (X = X'At (L1) + 1); --  Should be rejected, L1 is hidden by the assert and cut
      Y := X;
   end Assert_And_Cut_5;

   procedure Assert_And_Cut_6 (X : in out Integer) is
      Y : Integer;
   begin
      <<L1>>
      X := X + 1;
      pragma Assert_And_Cut (X = 15);
      Y := X'At (L1); --  OK, L1 is at the beginning of the block
   end Assert_And_Cut_6;

   --  References to At should not cross loop invariants

   procedure Loop_Invariant_1 (X : in out Integer) is
   begin
      for I in 1 .. 100 loop
         X := X / 2;
         <<L1>>
         X := X + 1;
         pragma Loop_Invariant (X = X'At (L1) + 1);--  Should be rejected, L1 is before the invariant
      end loop;
   end Loop_Invariant_1;

   procedure Loop_Invariant_2 (X : in out Integer) is
   begin
      for I in 1 .. 100 loop
         X := X / 2;
         <<L1>>
         begin
            X := X + 1;
            pragma Loop_Invariant (X = X'At (L1) + 1);--  Should be rejected, L1 is before the invariant
         end;
      end loop;
   end Loop_Invariant_2;

   procedure Loop_Invariant_3 (X : in out Integer) is
      Y : Integer;
   begin
      for I in 1 .. 100 loop
         X := X / 2;
         begin
            <<L1>>
            X := X + 1;
            pragma Loop_Invariant (X >= 0);
            Y := X'At (L1); --  Should be rejected, L1 is before the invariant
         end;
      end loop;
   end Loop_Invariant_3;

   procedure Loop_Invariant_4 (X : in out Integer) is
      Y : Integer;
   begin
      for I in 1 .. 100 loop
         X := X / 2;
         <<L1>>
         X := X + 1;
         begin
            pragma Loop_Invariant (X >= 0);
            Y := X'At (L1); --  Should be rejected, L1 is before the invariant
         end;
      end loop;
   end Loop_Invariant_4;

   procedure Loop_Invariant_5 (X : in out Integer) is
      Y : Integer;
   begin
      for I in 1 .. 100 loop
         X := X / 2;
         <<L1>>
         X := X + 1;
         pragma Loop_Invariant (X >= 0);
         begin
            Y := X'At (L1); --  Should be rejected, L1 is before the invariant
         end;
      end loop;
   end Loop_Invariant_5;

   procedure Loop_Invariant_6 (X : in out Integer) is
      Y : Integer;
   begin
      for I in 1 .. 100 loop
         X := X / 2;
         <<L1>>
         X := X + 1;
         begin
            pragma Loop_Invariant (X >= 0);
         end;
         Y := X'At (L1); --  Should be rejected, L1 is before the invariant
      end loop;
   end Loop_Invariant_6;

   procedure Loop_Invariant_7 (X : in out Integer) is
      Y : Integer;
   begin
      for I in 1 .. 100 loop
         X := X / 2;
         pragma Loop_Invariant (X >= 0);
         <<L1>>
         X := X + 1;
         Y := X'At (L1); --  OK, L1 and the reference are after the invariant
      end loop;
   end Loop_Invariant_7;

   procedure Loop_Invariant_8 (X : in out Integer) is
      Y : Integer;
   begin
      for I in 1 .. 100 loop
         X := X / 2;
         <<L1>>
         X := X + 1;
         Y := X'At (L1); --  OK, L1 and the reference are before the invariant
         pragma Loop_Invariant (X >= 0);
      end loop;
   end Loop_Invariant_8;

   procedure Loop_Invariant_9 (X : in out Integer) is
      Y : Integer;
   begin
      for I in 1 .. 100 loop
         X := X / 2;
         <<L1>>
         X := X + 1;
         for J in 1 .. 100 loop
            pragma Loop_Invariant (X >= 0);
            Y := X'At (L1); --  OK, L1 is before the loop
         end loop;
      end loop;
   end Loop_Invariant_9;

   procedure Loop_Invariant_10 (X : in out Integer) is
      Y : Integer;
   begin
      for I in 1 .. 100 loop
         <<L1>>
         begin
            Y := X'At (L1); --  OK, we are before the invariant
            pragma Loop_Invariant (X >= 0);
         end;
      end loop;
   end Loop_Invariant_10;

   procedure Loop_Invariant_11 (X : in out Integer) is
      Y : Integer;
   begin
      for I in 1 .. 100 loop
         <<L1>>
         begin
            begin
               if I mod 2 = 0 then
                  for J in 1 .. 100 loop
                     begin
                        pragma Loop_Invariant (X >= 0);
                        Y := X'At (L1); --  OK, we are before the invariant in the outer loop
                     end;
                  end loop;
               end if;
               pragma Loop_Invariant (X >= 0);
            end;
         end;
      end loop;
   end Loop_Invariant_11;

   --  If the prefix of At is an allocating function call, it should be in a
   --  pragma or constant declaration.

   type Int_Access is access Integer;

   type Int_Cst_Access is access constant Integer;

   type Int_Access_Wrapper is record
      R : Int_Access;
   end record;

   type Int_Access_Wrapper_Cst_Access is access constant Int_Access_Wrapper;

   function Allocate (X : Integer) return Int_Access is
   begin
      return new Integer'(X);
   end Allocate;

   procedure Test_Allocate_1 is
      X : Integer := 12;
      Y : Int_Access;
   begin
      <<L1>>
      X := 13;
      Y := Allocate (X)'At (L1); --  Should be rejected, Y is a variable
   end Test_Allocate_1;

   procedure Test_Allocate_2 is
      X : Integer := 12;
      Y : Int_Access;
   begin
      <<L1>>
      X := 13;
      pragma Assert (Allocate (X)'At (L1).all = 12); --  OK, At on allocating function in pragma
   end Test_Allocate_2;

   procedure Test_Allocate_3 is
      X : Integer := 12;
   begin
      <<L1>>
      X := 13;
      declare
         Y : constant Int_Access_Wrapper := (R => Allocate (X)'At (L1)); --  OK, At on allocating function in constant declaration
      begin
         null;
      end;
   end Test_Allocate_3;

   procedure Test_Allocate_4 is
      X : Integer := 12;
   begin
      <<L1>>
      X := 13;
      declare
         Y : constant Int_Access := Allocate (X)'At (L1); --  Should be rejected, the value designated by Y is a variable
      begin
         null;
      end;
   end Test_Allocate_4;

   procedure Test_Allocate_5 is
      X : Integer := 12;
      Y : Int_Cst_Access;
   begin
      <<L1>>
      X := 13;
      Y := Int_Cst_Access (Allocate (X)'At (L1)); --  OK, At on allocating function in move to constant
   end Test_Allocate_5;

   procedure Test_Allocate_6 is
      X : Integer := 12;
      Y : Int_Access_Wrapper_Cst_Access;
   begin
      <<L1>>
      X := 13;
      Y := new Int_Access_Wrapper'(R => Allocate (X)'At (L1)); --  OK, At on allocating function in move to constant
   end Test_Allocate_6;
begin
   null;
end;
