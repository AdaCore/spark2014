procedure Test_Equal is
   pragma SPARK_Mode(On);

   type My_Int is new Integer range 0 .. 7;

   type My_Int_Mod is record
      Content : My_Int;
   end record;

   type My_Rec is record
      Content : My_Int_Mod;
   end record;

   function "=" (X, Y : My_Int_Mod) return Boolean is
     (X.Content = Y.Content or else
        (if X.Content < Y.Content then Y.Content - X.Content = 4
         else X.Content - Y.Content = 4));

   Content_X : constant My_Int_Mod := My_Int_Mod'(Content => 1);
   Content_Y : constant My_Int_Mod := My_Int_Mod'(Content => 5);

   X : constant My_Rec := My_Rec'(Content => Content_X);
   Y : constant My_Rec := My_Rec'(Content => Content_Y);
begin
   pragma Assert (Content_X = Content_Y);
   pragma Assert (X /= Y);
end Test_Equal;
