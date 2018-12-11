package body Correlator is
   package body Tree is

      package List is

         type List_Private_Type is private;

         procedure Dummy;

      private

         type Element_Record_Type is null record;

         type List_Private_Type is access Element_Record_Type;

      end List;

      package body List is

         Available_Elements_List : List_Private_Type;

         procedure Dummy is null;

      end List;

      procedure Dummy is null;

   end Tree;
end Correlator;
