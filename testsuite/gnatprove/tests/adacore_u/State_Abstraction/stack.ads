package Stack with SPARK_Mode, Abstract_State => (The_Stack, P_Stack) is
   subtype Element is Positive;
   Max : constant Natural := 100;
   type Element_Array is array (Positive range <>) of Element;
   subtype Length_Type is Natural range 0 .. Max;
   Top : Length_Type := 0;
   Content : Element_Array (1 .. Max);
   pragma Unevaluated_Use_Of_Old (Allow);

   type Stack_Model is private;

   procedure Pop  (E : out Element) with
     Global  => (Input  => Content,
                 In_Out => Top),
     Depends => (Top => Top,
                 E   => (Content, Top));
   procedure Push (E : in  Element) with
     Global  => (In_Out => (Content, Top)),
     Depends => (Content => + (Content, Top, E),
                 Top     => Top);

   procedure Pop2  (E : out Element) with
     Global  => (In_Out       => The_Stack),
     Depends => ((The_Stack, E) => The_Stack);
   procedure Push2 (E : in  Element) with
     Global  => (In_Out    => The_Stack),
     Depends => (The_Stack => (The_Stack, E));

   procedure Push3 (E : in  Element) with
     Post => not Is_Empty and
     (if Is_Full'Old then Get_Stack = Get_Stack'Old else Peek = E);
   function Get_Stack return Stack_Model;
   function Peek return Element with
     Pre => not Is_Empty;
   function Is_Full return Boolean;
   function Is_Empty return Boolean;

   procedure Push4 (E : in  Element) with
     Post => not Is_Empty2 and
     (if Is_Full2'Old then Get_Stack2 = Get_Stack2'Old else Peek2 = E);
   function Get_Stack2 return Stack_Model;
   function Peek2 return Element with
     Pre => not Is_Empty2;
   function Is_Full2 return Boolean;
   function Is_Empty2 return Boolean;

private
   type Stack_Model is record
      Top     : Length_Type;
      Content : Element_Array (1 .. Max);
   end record;

   P_Top : Length_Type := 0 with Part_Of => P_Stack;
   P_Content : Element_Array (1 .. Max) with Part_Of => P_Stack;

   function Get_Stack2 return Stack_Model is ((P_Top, P_Content));
   function Peek2 return Element is (P_Content (P_Top));
   function Is_Full2 return Boolean is (P_Top >= Max);
   function Is_Empty2 return Boolean is (P_Top = 0);
end Stack;
