package FL1
  with SPARK_Mode => On
is
   pragma Elaborate_Body;

   type Root is tagged record
      F : Positive := 1;
   end record;

   procedure Reset_F (X : in out Root) with
     Post'Class => X.F = 1;
   procedure Incr_F (X : in out Root) with
     Pre'Class  => X.F <= Integer'Last / 10,
     Post'Class => X.F > X.F'Old; --@POSTCONDITION:FAIL

   type Child is private;

   function Get_F (X : Child) return Positive;
   procedure Incr_F (X : in out Child) with
     Pre => Get_F (X) < Integer'Last;

   type Bad_Child1 is private;

   function Get_F (X : Bad_Child1) return Positive;
   procedure Incr_F (X : in out Bad_Child1) with
     Pre => Get_F (X) < Integer'Last / 100; --@WEAKER_PRE:FAIL

   procedure Reset_F (X : in out Bad_Child1) with
     Pre => Get_F (X) /= 1; --@TRIVIAL_PRE:FAIL

   type Bad_Child2 is private;

   procedure Incr_F (X : in out Bad_Child2);

   type Bad_Child3 is private;

   procedure Incr_F (X : in out Bad_Child3) with
     Post => X = X'Old; --@STRONGER_POST:FAIL

private
   type Child is new Root with record
      G : Boolean := True;
   end record;
   function Get_F (X : Child) return Positive is (X.F);
   type Bad_Child1 is new Root with record
      G : Boolean := True;
   end record;
   function Get_F (X : Bad_Child1) return Positive is (X.F);
   type Bad_Child2 is new Root with record
      G : Boolean := True;
   end record;
   type Bad_Child3 is new Root with record
      G : Boolean := True;
   end record;
end FL1;
