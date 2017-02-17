pragma SPARK_Mode;

package HTML_Page with
  Abstract_State => (Content, Style_Sheet)
is
   type Item is new Integer;

   procedure Initialize_Content with
     Global => (Output => Content);

   procedure Update_Content (New_Item : Item) with
     Global => (In_Out => Content);

   procedure Display_Text with
     Global => (Input => (Content, Style_Sheet));
end HTML_Page;
