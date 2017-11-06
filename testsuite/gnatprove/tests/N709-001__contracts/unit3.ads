with Unit2; use Unit2;

package Unit3 with
  SPARK_Mode
is
   pragma Elaborate_Body;
   type T3 is new T2 with record
      C3 : Integer;
   end record;

   procedure Create (X : out T3) with
     Post'Class => X.C1 = 0 and then X.C2 = 0 and then X.C3 = 0,
     Post       => X.C1 = 0 and then X.C2 = 0 and then X.C3 = 0;

   function Is_Max (X : T3) return Boolean is
      (T2(X).Is_Max or else X.C3 = Integer'Last);

   function Is_Zero (X : T3) return Boolean is
      (T2(X).Is_Zero and then X.C3 = 0);

   function Next (X : T3) return T3;

   procedure Bump (X : in out T3) with
     Pre'Class  => not X.Is_Max,
     Post'Class => X.C1 = X.C1'Old + 1 and then X.C2 = X.C2'Old + 1 and then X.C3 = X.C3'Old + 1,
     Post       => X.C1 = X.C1'Old + 1 and then X.C2 = X.C2'Old + 1 and then X.C3 = X.C3'Old + 1;

private
   function Next (X : T3) return T3 is
      (T3'(T2(X).Next with C3 => X.C3 + 1))
   with SPARK_Mode => Off;  --  until tagged aggregates are supported

end Unit3;
