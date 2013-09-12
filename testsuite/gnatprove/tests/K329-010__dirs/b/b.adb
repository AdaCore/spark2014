with A;

procedure B is pragma SPARK_Mode (On);
   X : A.T;
begin
   X := A.any;
   pragma Assert (X > 2);
end B;

