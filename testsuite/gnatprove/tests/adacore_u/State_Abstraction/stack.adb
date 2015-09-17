package body Stack with SPARK_Mode,
  Refined_State => (The_Stack => (B_Top, B_Content),
                    P_Stack   => (P_Top, P_Content)) is
   B_Top : Length_Type := 0;
   B_Content : Element_Array (1 .. Max);

   procedure Pop  (E : out Element) is
   begin
      E := Content (Top);
      Top := Top - 1;
   end Pop;
   procedure Push (E : in  Element) is
   begin
      Top := Top + 1;
      Content (Top) := E;
   end Push;

   procedure Pop2  (E : out Element) with
     Refined_Global  => (Input  => B_Content,
                         In_Out => B_Top),
     Refined_Depends => (B_Top => B_Top,
                         E   => (B_Content, B_Top)) is
   begin
      E := B_Content (B_Top);
      B_Top := B_Top - 1;
   end Pop2;
   procedure Push2 (E : in  Element) with
     Refined_Global  => (In_Out => (B_Content, B_Top)),
     Refined_Depends => (B_Content => + (B_Content, B_Top, E),
                         B_Top     => B_Top) is
   begin
      B_Top := B_Top + 1;
      B_Content (B_Top) := E;
   end Push2;

   procedure Push3 (E : in  Element) is
   begin
      if B_Top >= Max then
         return;
      end if;
      B_Top := B_Top + 1;
      B_Content (B_Top) := E;
   end Push3;
   function Get_Stack return Stack_Model is ((B_Top, B_Content));
   function Peek return Element is (B_Content (B_Top));
   function Is_Full return Boolean is (B_Top >= Max);
   function Is_Empty return Boolean is (B_Top = 0);

   procedure Push4 (E : in  Element) is
   begin
      if P_Top >= Max then
         return;
      end if;
      P_Top := P_Top + 1;
      P_Content (P_Top) := E;
   end Push4;
end Stack;
