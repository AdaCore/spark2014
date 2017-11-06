with Unit1; use Unit1;

package Unit2 with
  SPARK_Mode
is
   pragma Elaborate_Body;
   type T2 is new T1 with record
      C2 : Integer;
   end record;

   procedure Create (X : out T2) with
     Post => X.C1 = 0 and then X.C2 = 0;

   function Is_Max (X : T2) return Boolean is
      (T1(X).Is_Max or else X.C2 = Integer'Last);

   function Is_Zero (X : T2) return Boolean is
      (T1(X).Is_Zero and then X.C2 = 0);

   function Next (X : T2) return T2;

   procedure Bump (X : in out T2) with
     Post => X.C1 = X.C1'Old + 1 and then X.C2 = X.C2'Old + 1;

private
   function Next (X : T2) return T2 is
      (T2'(T1(X).Next with C2 => X.C2 + 1))
   with SPARK_Mode => Off;  --  until tagged aggregates are supported

end Unit2;
