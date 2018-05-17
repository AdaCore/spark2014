package body Conts with SPARK_Mode => Off is

   package body Indefinite_Elements_Traits_SPARK with SPARK_Mode => Off is
      package body Private_Element_Access with SPARK_Mode => Off is
         procedure Unchecked_Deallocation is new Ada.Unchecked_Deallocation
           (Element_Type, Element_Access);

         procedure Unchecked_Free (X : in out Element_Access) is
         begin
            Unchecked_Deallocation (X);
         end Unchecked_Free;
      end Private_Element_Access;
   end Indefinite_Elements_Traits_SPARK;

   package body Indefinite_Elements_Traits is

      -------------
      -- Release --
      -------------

      procedure Release (E : in out Element_Access) is
      begin
         Free (E.all);
         Unchecked_Free (E);
      end Release;
   end Indefinite_Elements_Traits;

end Conts;
