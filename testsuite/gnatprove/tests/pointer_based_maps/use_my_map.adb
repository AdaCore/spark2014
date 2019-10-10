with My_Map; use My_Map;
procedure Use_My_Map with SPARK_Mode is
   procedure My_Replace_Element (M : access Map; K : Positive; V : Integer) with
     Pre  => Model_Contains (M, K),
     Post => Model_Contains (M, K) and then Model_Value (M, K) = V;

   procedure My_Replace_Element (M : access Map; K : Positive; V : Integer) is
      X : constant access Integer := Reference (M, K);
   begin
      X.all := V;
   end My_Replace_Element;
begin
   null;
end Use_My_Map;
