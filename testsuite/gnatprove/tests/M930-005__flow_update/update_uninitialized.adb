package body Update_Uninitialized
  with SPARK_Mode
is
   procedure LHS_Uninitialized (Choise  : in     Integer;
                                Element :    out Arr_Range;
                                Arr     : in out Arr_T)
   is
   begin
      if Choise < 0 then
         Element := 1;
      elsif Choise > 0 then
         Element := 2;
      end if;
      -- Apparently we missed the Choise = 0 case...
      Arr := Arr'Update (Element => 0);  --  warning: Element might be uninitialized
      Element := 3;
   end LHS_Uninitialized;

   procedure RHS_Uninitialized (Choise  : in     Integer;
                                Element :    out Arr_Range;
                                Arr     : in out Arr_T)
   is
   begin
      if Choise < 0 then
         Element := 1;
      elsif Choise > 0 then
         Element := 2;
      end if;
      -- Apparently we missed the Choise = 0 case...
      Arr := Arr'Update (1 => Integer (Element));  --  warning: Element might be uninitialized
      Element := 3;
   end RHS_Uninitialized;
end Update_Uninitialized;
