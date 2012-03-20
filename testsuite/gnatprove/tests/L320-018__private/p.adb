pragma Ada_12;
procedure P (V : Integer) is
    package Pack is
       type T1 is private;
       function F (X : T1) return T1 is (X);
    private
       package Inner is
          type T2 is private;
       private
          type T3 is range 1 .. 10;
          type T2 is record
             X : T3;
          end record;
       end Inner;
       type T1 is new Inner.T2;
    end Pack;

    X : Pack.T1;
begin
    X := X;
end P;
