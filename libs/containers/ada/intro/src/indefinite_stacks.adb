package body Indefinite_Stacks is

   function Create (Default : Content_Ref) return Stack_Ptr  is
      output : aliased Stack_Ptr := new Stack'(Default, null, null);
   begin
      return output;
   end Create;

   function Is_Empty (S : Stack_Ptr) return Boolean is
   begin
      if S = null then
         return True;
      elsif  S.Previous = null
        and S.Next = null
        and S.Element = null then
         return True;
      else
         return False;
      end if;
   end Is_Empty;

   function Peek (S : Stack_Ptr) return Content_Ref is
      output : Content_Ref := S.Element;
   begin
      return output;
   end Peek;

   function Pop (S : in out Stack_Ptr) return Content_Ref is
      output : Content_Ref := S.Element;
      T : Stack_Ptr := S.Previous;
   begin
      S.Previous := null;  --  not required
      S.Element := null; --  not required
      Free_Stack (S.Element);
      S := T;

      --  Cleaning the used slot

      if S /= null then
         S.Next := null;
      end if;
      return output;
   end Pop;

   procedure Pop (S : in out Stack_Ptr; X : out Content_Ref)  is
      T : Stack_Ptr := S.Previous;
   begin
      X := S.Element;
      S.Previous := null;  --  Not required
      S.Element := null; --  Not required
      Free_Stack (S.Element);

      --  Cleaning the used slot

      S := T;
      if S /= null then
         S.Next := null;
      end if;
   end Pop;

   function Push (S : Stack_Ptr; X : Content_Ref) return Stack_Ptr is
      output : Stack_Ptr := S;
   begin
      Push (output, X);
      return output;
   end Push;

   procedure Push (S : in out Stack_Ptr; X : Content_Ref) is
      T : Stack_Ptr := new Stack'(Element => X, Previous => S, Next => null);
   begin
      S.Next := T;
      S := T;
   end Push;

   --  Push a new element on the stack FIFO

end Indefinite_Stacks;
