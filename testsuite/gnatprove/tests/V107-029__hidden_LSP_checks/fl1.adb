package body FL1
with SPARK_Mode => On
is
   procedure Reset_F (X : in out Root) is
   begin
      X.F := 1;
   end Reset_F;

   procedure Incr_F (X : in out Root) is
   begin
      X.F := X.F * 10;
   end Incr_F;

   procedure Incr_F (X : in out Child) is
   begin
      X.F := X.F + 1;
   end Incr_F;

   procedure Incr_F (X : in out Bad_Child1) is
   begin
      X.F := X.F * 100;
   end Incr_F;

   procedure Reset_F (X : in out Bad_Child1) is
   begin
      X.F := 1;
   end Reset_F;

   procedure Incr_F (X : in out Bad_Child2) is null;

   procedure Incr_F (X : in out Bad_Child3) is null;

end FL1;
