procedure P is 
   function Id (X : Float) return Float is (X);
   type T is new Float range Id(0.0) .. Id(1.0);
   Y : T := 1.5;
begin
   null;
end P;
