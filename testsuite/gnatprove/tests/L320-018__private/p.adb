pragma Ada_12;
procedure P (V : Integer) is pragma SPARK_Mode (Off);  --  conversion composite
    package Pack is
       type T1 is private;
       Null_T1 : constant T1;
       function F (X : T1) return T1 is (X);
    private
       package Inner is
          type T2 is private;
          Null_T2 : constant T2;
       private
          type T3 is range 1 .. 10;
          type T2 is record
             X : T3;
          end record;
          Null_T2 : constant T2 := T2'(X => 5);
       end Inner;
       type T1 is new Inner.T2;
       Null_T1 : constant T1 := T1 (Inner.Null_T2);
    end Pack;

    X : Pack.T1;
begin
    X := X;
end P;
