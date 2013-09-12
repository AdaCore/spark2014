package MaxAndSum is pragma SPARK_Mode (On); 

   N : constant Natural := 100;
   subtype Element is Natural range 0 .. 100;
   type ElementArray is array (Element) of Positive range 1 .. N;

   procedure MaxAndSum (A : ElementArray; Sum : out Natural; Max : out Element)
   with Post => Sum <= N*Max;

end MaxAndSum;
