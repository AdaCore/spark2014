package Generic_Packages is
   type Bad is access Positive;

   generic
      type Element is range <>;
   package Gen_Add with SPARK_Mode is
      function Add (E1, E2 : Element) return Element with
        Pre => (if E1 > 0 then Element'Last - E1 >= E2
                  else Element'First - E1 <= E2);
   private
      pragma SPARK_Mode (Off);
      function Add (E1, E2 : Element) return Element is (E1 + E2);
      type Bad is access Element;
   end Gen_Add;

   generic
      type Element is range <>;
      type Element_Array is array (Positive range <>) of Element;
      with package Element_Add is new Gen_Add (Element => Element);
   package Gen_Sum with SPARK_Mode is
      function Sum (A : Element_Array) return Element with
        Pre => 0 in Element;
   end Gen_Sum;
end Generic_Packages;
