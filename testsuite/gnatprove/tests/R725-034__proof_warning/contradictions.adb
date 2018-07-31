package body Contradictions
with SPARK_Mode => On
is

   -------
   -- P --
   -------

   procedure P
     (V : out Integer)
   is
   begin
      V := -1;
   end P;

   procedure P2 (V : in out Integer) is
   begin
      V := V * 2;
   end P2;

   procedure P3
     (V : out Integer)
   is
   begin
      V := -1;
   end P3;

   procedure P4 (V : out A) is
   begin
      V := (others => 99);
   end P4;

   procedure P5 (V : in out Integer) is
   begin
      V := -1;
   end P5;

   procedure P6 (V : in out Integer) is
   begin
      V := -1;
   end P6;

   procedure P7 (V : in out Integer) is
   begin
      V := -1;
   end P7;

   procedure P8 (V : in out Integer) is
   begin
      V := -1;
   end P8;

end Contradictions;
