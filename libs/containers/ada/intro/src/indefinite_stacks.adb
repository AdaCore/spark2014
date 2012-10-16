package body Indefinite_Stacks is

   function Compare (S, T : Stack) return Boolean is
      U : Stack := Get_First (S).all;
      V : Stack := Get_First (T).all;
   begin
      while U.Next /= null and V.Next /= null loop
         if U.Element /= V.Element then
            return False;
         end if;
         U := U.Next.all;
         V := V.Next.all;
      end loop;
      if U.Next /= null or V.Next /= null      -- when U or V is larger
        or U.Element /= V.Element then         -- last comparation
         return False;
      end if;
      return True;
   end Compare;
   function Create return Stack  is
      --      output : Stack;
   begin
      --      output.Previous := null;
      --      output.Next := null;
      --      output.Element := Default_Value;
      --      return output;
      return output : Stack do
         output.Previous := null;
         output.Next := null;
      end return;
      --      begin
      --      return (Controlled with   Element => ,
      --              Previous | Next => null);
   end Create;

   function Get_First (S : Stack) return Stack_Ptr is
      output : Stack_Ptr := null;
   begin
      output.all := S;
      while S.Previous /= null loop
         output.all := S.Previous.all;
      end loop;
      return output;
   end Get_First;

   function Get_Last (S : Stack) return Stack_Ptr is
      output : Stack_Ptr := null;
   begin
      output.all := S;
      while S.Next /= null loop
         output.all := S.Next.all;
      end loop;
      return output;
   end Get_Last;

   function Is_Empty (S : Stack) return Boolean is
   begin
      if S.Previous = null and S.Next = null then
         return True;
      end if;
      return False;
   end Is_Empty;

   function Peek (S : Stack) return Item_Type is
--      output : Item_Type;
   begin
--      output := Get_Last (S).Element;
--      return output;
      return (Get_Last (S).Element);
   end Peek;

   function Pop (S : in out Stack) return Item_Type is
      output : Item_Type;
   begin
      Pop (S, output);
      return output;
   end Pop;

   procedure Pop (S : in out Stack; X : out Item_Type) is
      Last_One, Temp : Stack_Ptr := Get_Last (S);
   begin
      X := Last_One.Element;
      Temp := Last_One.Previous;
      Temp.Next := null;
      Last_One.Previous := null;    -- Not required
      --  Free_Item (Last_One.Element);
      Free_Stack (Last_One);

      --  Cleaning the used slot

   end Pop;

   function Push (S : Stack; X : Item_Type) return Stack is
      output : Stack := S;
      Old_Last : Stack_Ptr :=  Get_Last (output);
      New_Stack : Stack := Stack'(Controlled with
                                  Element => X,
                                  Previous => Old_Last,
                                  Next => null);
   begin
      Old_Last.Next.all := New_Stack;
      return output;
   end Push;

   procedure Push (S : in out Stack; X : Item_Type) is
      Old_Last : Stack_Ptr :=  Get_Last (S);
      New_Stack : Stack := Stack'(Controlled with
                                  Element => X,
                                  Previous => Old_Last,
                                  Next => null);
   begin
      Old_Last.Next.all := New_Stack;
   end Push;

   --  Push a new element on the stack FIFO

   procedure Adjust (Object : in out Stack) is
--      First_One : Stack_Ptr := Get_First (Object);
      First_One : Stack_Ptr := Object'Unchecked_Access;
      Current, Past, Tmp : Stack_Ptr := null;
   begin
      Current := First_One;
      --      while Current.Next /= null loop
      --         Tmp := Current.Next;
      --         Past := Current;
      --         Current.Next := new Stack'(Controlled with
      --                                  Element => Tmp.Element,
      --                                  Previous => Past,
      --                                  Next => Tmp.Next);
      --         Current := Current.Next;
      --      end loop;
   end Adjust;

   procedure Finalize (Object : in out Stack) is
      First_One : Stack_Ptr := Get_First (Object);
      Last_One : Stack_Ptr := Get_Last (Object);
   begin
      --  idempotent operations:
      while First_One /= Last_One loop
         Free_Stack (Last_One);
         Last_One := Get_Last (Object);
      end loop;
   end Finalize;

end Indefinite_Stacks;
