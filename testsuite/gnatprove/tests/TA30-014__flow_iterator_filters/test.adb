with Ada.Containers.Functional_Vectors;

procedure Test with SPARK_Mode is

   Y : Integer := 0;
   Z : Integer := 0;

   function P (X : Integer) return Boolean with Import, Global => (Input => Y);

   --  Loop parameter specification tests

   type My_Arr is array (Positive range <>) of Integer;

   procedure LPS_Bad_Global (A : My_Arr) with
     Global => null
   is
   begin
      for K in A'Range when P (K) loop
         null;
      end loop;
   end LPS_Bad_Global;

   procedure LPS_OK_Global (A : My_Arr) with
     Global => (Input => Y)
   is
   begin
      for K in A'Range when P (K) loop
         null;
      end loop;
   end LPS_OK_Global;

   procedure LPS_Bad_Depends (A : My_Arr) with
     Global => (Input => Y, In_Out => Z),
     Depends => (Z => (A, Z), null => Y)
   is
   begin
      for K in A'Range when P (K) loop
         Z := Z + 1;
      end loop;
   end LPS_Bad_Depends;

   procedure LPS_OK_Depends (A : My_Arr) with
     Global => (Input => Y, In_Out => Z),
     Depends => (Z => (A, Y, Z))
   is
   begin
      for K in A'Range when P (K) loop
         Z := Z + 1;
      end loop;
   end LPS_OK_Depends;

   procedure LPS_Init (A : My_Arr; B : out Integer) is
   begin
      for K in A'Range when P (K) loop
         B := 0;
      end loop;
   end LPS_Init;

   --  Quantified expression tests

   procedure QE_LPS_Bad_Global (A : My_Arr) with
     Global => null
   is
   begin
      pragma Assert (for all K in A'Range when P (K) => True);
   end QE_LPS_Bad_Global;

   procedure QE_LPS_OK_Global (A : My_Arr) with
     Global => (Proof_In => Y)
   is
   begin
      pragma Assert (for all K in A'Range when P (K) => True);
   end QE_LPS_OK_Global;

   procedure QE_LPS_Bad_Depends (A : My_Arr) with
     Global => (Input => Y, In_Out => Z),
     Depends => (Z => (A, Z), null => Y)
   is
      OK : Boolean := (for all K in A'Range when P (K) => True);
   begin
      if OK then
         Z := 1;
      end if;
   end QE_LPS_Bad_Depends;

   procedure QE_LPS_OK_Depends (A : My_Arr) with
     Global => (Input => Y, In_Out => Z),
     Depends => (Z => (A, Y, Z))
   is
      OK : Boolean := (for all K in A'Range when P (K) => True);
   begin
      if OK then
         Z := 1;
      end if;
   end QE_LPS_OK_Depends;

   package My_Sequences is new Ada.Containers.Functional_Vectors
     (Index_Type   => Positive,
      Element_Type => Integer);
   type My_Seq is new My_Sequences.Sequence;

   procedure QE_IS_Bad_Global (A : My_Seq) with
     Global => null
   is
   begin
      pragma Assert (for all K in A when P (K) => True);
   end QE_IS_Bad_Global;

   procedure QE_IS_OK_Global (A : My_Seq) with
     Global => (Proof_In => Y)
   is
   begin
      pragma Assert (for all K in A when P (K) => True);
   end QE_IS_OK_Global;

   procedure QE_IS_Bad_Depends (A : My_Seq) with
     Global => (Input => Y, In_Out => Z),
     Depends => (Z => (A, Z), null => Y)
   is
      OK : Boolean := (for all K in A when P (K) => True);
   begin
      if OK then
         Z := 1;
      end if;
   end QE_IS_Bad_Depends;

   procedure QE_IS_OK_Depends (A : My_Seq) with
     Global => (Input => Y, In_Out => Z),
     Depends => (Z => (A, Y, Z))
   is
      OK : Boolean := (for all K in A when P (K) => True);
   begin
      if OK then
         Z := 1;
      end if;
   end QE_IS_OK_Depends;

begin
   null;
end Test;
