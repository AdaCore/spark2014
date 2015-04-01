--  with Ada.Text_IO; use Ada.Text_IO;

procedure Size_Attr is
   pragma SPARK_Mode (On);

   subtype My_Int is Integer range 1 .. 10;

   --  Empty record
   type R is record
      null;
   end record;

   --  Variant record (see GNAT RM 9.4)
   type R1 (A : Boolean := False) is record
      case A is
	 when True  => X : Character;
	 when False => null;
      end case;
   end record;

   --  Variant record subtype
   subtype R1F is R1 (False);

   --  Simple record
   type R2 is record
      X : Integer;
   end record;

   type R3 is tagged record
      X : Integer;
   end record;

   type R4 is new R3 with
      record
         Y : Integer;
      end record;

   --  Arrays: constrained and not
   type Constrained_Array is array (My_Int) of Natural;
   type Unconstrained_Array is array (Positive range <>) of Natural;

   type Constrained_Array_2 is array (My_Int, My_Int) of Natural;
   type Unconstrained_Array_2 is array (Positive range <>,
					Positive range <>) of Natural;

   type Constrained_Array_3 is array (My_Int, My_Int, My_Int) of Natural;
   type Unconstrained_Array_3 is array (Positive range <>,
					Positive range <>,
					Positive range <>) of Natural;

   type Constrained_Array_4 is array (My_Int, My_Int,
				      My_Int, My_Int) of Natural;
   type Unconstrained_Array_4 is array (Positive range <>,
					Positive range <>,
					Positive range <>,
					Positive range <>) of Natural;


   --  Objects
   B : Boolean := False;
   I : Integer := 0;
   S : String := "abc";

   MI : My_Int := My_Int'First;

   V : R;
   V1 : R1 (False);
   V2 : R1;
   V3 : R1F;
   V4 : R2 := (X => 1);
   V5 : R3;
   V6 : R4;

   Ca : Constrained_Array := (others => 1);
   Ua : Unconstrained_Array (1 .. 5) := (others => 1);

   Ca2 : Constrained_Array := (others => 1);
   Ca3 : Constrained_Array := (others => 1);
   Ca4 : Constrained_Array := (others => 1);

   Ua2 : Unconstrained_Array_2 (1 .. 5, 1 .. 5) :=
     (others => (others => 1));
   Ua3 : Unconstrained_Array_3 (1 .. 5, 1 .. 5, 1 .. 5) :=
     (others => (others => (others => 1)));
   Ua4 : Unconstrained_Array_4 (1 .. 5, 1 .. 5, 1 .. 5, 1 .. 5) :=
     (others => (others => (others => (others => 1))));

begin

   --  Test cases for Type'Size

   --  scalar types are apparently handled by constant folding in the front-end
   pragma Assert (Boolean'Size = 1);
   pragma Assert (Integer'Size = 32);

   pragma Assert (My_Int'Size >= 0);

   --  record types
   pragma Assert (R'Size >= 0);   --  empty
   pragma Assert (R1'Size >= 0);  --  variant
   pragma Assert (R1F'Size >= 0); --  constrained variant
   pragma Assert (R2'Size >= 0);  --  fixed
   pragma Assert (R3'Size >= 0);  --  tagged
   pragma Assert (R4'Size >= 0);  --  extended

   -- attribute 'Class is not permitted in SPARK
   --  pragma Assert (R4'Class'Size >= 0);

   --  arrays
   pragma Assert (Constrained_Array'Size >= 0);
   pragma Assert (Unconstrained_Array'Size >= 0);
   pragma Assert (String'Size >= 0);

   pragma Assert (Constrained_Array_2'Size >= 0);
   pragma Assert (Constrained_Array_3'Size >= 0);
   pragma Assert (Constrained_Array_4'Size >= 0);
   pragma Assert (Unconstrained_Array_2'Size >= 0);
   pragma Assert (Unconstrained_Array_3'Size >= 0);
   pragma Assert (Unconstrained_Array_4'Size >= 0);

   -- Test cases for Obj'Size

   pragma Assert (B'Size = 8);    -- scalars
   pragma Assert (I'Size = 32);
   pragma Assert (Mi'Size >= 0);

   pragma Assert (S'Size >= 0);   -- arrays
   pragma Assert (Ca'Size >= 0);
   pragma Assert (Ua'Size >= 0);

   pragma Assert (Ca2'Size >= 0);
   pragma Assert (Ua2'Size >= 0);
   pragma Assert (Ca3'Size >= 0);
   pragma Assert (Ua3'Size >= 0);
   pragma Assert (Ca4'Size >= 0);
   pragma Assert (Ua4'Size >= 0);

   pragma Assert (V'Size >= 0);
   pragma Assert (V1'Size >= 0);
   pragma Assert (V2'Size >= 0);
   pragma Assert (V3'Size >= 0);
   pragma Assert (V4'Size >= 0);
   pragma Assert (V5'Size >= 0);
   pragma Assert (V6'Size >= 0);

   null;
end Size_Attr;
