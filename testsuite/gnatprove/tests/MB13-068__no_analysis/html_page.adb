pragma SPARK_Mode;

package body HTML_Page with
  Refined_State => (Content     => (Header, Content_Body, Footer),
                    Style_Sheet => (Background, Fonts, Title_Styles))
is
   subtype HTML_Section is Integer;
   subtype Color is Integer;
   subtype List_Of_Fonts is Integer;
   subtype List_Of_Styles is Integer;

   Header       : HTML_Section := 0;
   Content_Body : HTML_Section := 0;
   Footer       : HTML_Section := 0;
   Background   : Color := 0;
   Fonts        : List_Of_Fonts := 0;
   Title_Styles : List_Of_Styles := 0;

   procedure Initialize_Content with
     Refined_Global => (Output => (Header, Content_Body, Footer)) is
   begin
      Content_Body := Header;
   end Initialize_Content;

   procedure Update_Content (New_Item : Item) with
     Refined_Global => (In_Out => Content_Body) is
   begin
      Content_Body := Content_Body;
   end Update_Content;

   procedure Display_Text with
     Refined_Global => (Input => (Content_Body, Fonts, Title_Styles))
   is
      X : Integer := Content_Body + Title_Styles;
      pragma Unreferenced (X);
   begin
      null;
   end Display_Text;

end HTML_Page;
