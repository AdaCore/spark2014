package Discrete is

   --  Color

   type Color is (Red, Green, Blue, Cyan, Magenta, Yellow);

   type Color_Kind is (Primary, Secondary);

   type Thing is (Blood, Grass, Sea, Sky, Flower, Sun);

   function Get_Color_Of_Thing (T : Thing) return Color;

   --  Time

   type Day is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

   subtype Weekday is Day range Mon .. Fri;

   type Month is (Jan, Feb, Mar, Apr, May, Jun, Jul, Aug, Sep, Oct, Nov, Dec);

   subtype Spring is Month range Mar ..  Jun;

   --  With a choice list

   function In_Choice_List (C : Color) return Color_Kind;

   function Not_In_Choice_List (C : Color) return Color_Kind;

   function In_Choice_List_Left_Not_Static (T : Thing) return Color_Kind;

   function In_Choice_List_Right_Not_Static (C : Color) return Color_Kind;

   --  With a range

   function In_Range (C : Color) return Color_Kind;

   function Not_In_Range (C : Color) return Color_Kind;

   --  With subtypes

   function In_Subtype (D : Day) return Boolean;

   function Not_In_Subtype (D : Day) return Boolean;

   --  Mix

   function Mix (M : Month) return Boolean;

end Discrete;
