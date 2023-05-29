package body P is  pragma SPARK_Mode (On);

   procedure Identity (L : in out Map; K : Key_Type) is
   begin
      Insert (L, K, 1);
      Delete (L, K);
   end Identity;

   procedure Nearly_Identity (L : in out Map; K : Key_Type) is
      E  : Element_Type := Element (L, K);
      L0 : Map := Copy (L) with Ghost;
   begin
      Delete (L, K);
      Insert (L, K, E);
      pragma Assert
        (if Find (L, K) = Find (L0, K) then
           (for all I of Positions (L) =>
              Formal_Model.P.Get (Positions (L0), I)
              = Formal_Model.P.Get (Positions (L), I)));
   end Nearly_Identity;

   procedure My_Include (L : in out Map; K : Key_Type; E : Element_Type) is
   begin
      if Contains (L, K) then
         Replace (L, K, E);
      else
         Insert (L, K, E);
      end if;
   end My_Include;

end P;
