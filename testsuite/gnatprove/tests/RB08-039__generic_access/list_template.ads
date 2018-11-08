generic
package List_Template is

   type List_Private_Type is private;

   procedure Dummy;

private

   type Element_Record_Type is null record;

   type List_Private_Type is access Element_Record_Type;

end List_Template;
