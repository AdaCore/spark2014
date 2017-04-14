package Unit1 with
  SPARK_Mode
is

   type T1 is tagged record
      C1 : Integer;
   end record;

   procedure Create (X : out T1) with
     Global => null,
     Post'Class => X.Is_Zero,
     Post       => X.C1 = 0;

   function Is_Max (X : T1) return Boolean is
      (X.C1 = Integer'Last)
   with Global => null;

   function Is_Zero (X : T1) return Boolean is
      (X.C1 = 0)
   with Global => null;

   function Next (X : T1) return T1
   with
      Global => null,
      Pre'Class => not X.Is_Max;

   procedure Bump (X : in out T1) with
     Global => null,
     Pre'Class  => not X.Is_Max,

     Post'Class => X = X'Old.Next,
     Post       => X.C1 = X.C1'Old + 1;

private
   function Next (X : T1) return T1 is
      (T1'(C1 => X.C1 + 1))
   with SPARK_Mode => Off;  --  until tagged aggregates are supported

end Unit1;
