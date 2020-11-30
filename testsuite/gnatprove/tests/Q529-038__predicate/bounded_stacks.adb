package body Bounded_Stacks is

   ------------
   -- Extent --
   ------------

   function Extent (This : Stack) return Natural is
     (This.Top);

   -----------
   -- Empty --
   -----------

   function Empty (This : Stack'Class) return Boolean is
     (This.Top = 0);

   ----------
   -- Full --
   ----------

   function Full (This : Stack) return Boolean is
     (This.Top = This.Capacity);

   -----------
   -- Reset --
   -----------

   procedure Reset (This : out Stack) is
   begin
      This.Top := 0;
   end Reset;

   ----------
   -- Push --
   ----------

   procedure Push (This : in out Stack;  Item : Element) is
   begin
      This.Top := This.Top + 1;
      This.Values (This.Top) := Item;
   end Push;

   ---------
   -- Pop --
   ---------

   procedure Pop (This : in out Stack;  Item : out Element) is
   begin
      Item := This.Values (This.Top);
      This.Top := This.Top - 1;
   end Pop;

   ----------
   -- Peek --
   ----------

   function Peek (This : Stack) return Element is
     (This.Values (This.Top));

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Stack) return Boolean is
   begin
      if Left.Top /= Right.Top then
         return False;
      else
         for K in 1 .. Left.Top loop
            if Left.Values (K) /= Right.Values (K) then
               return False;
            end if;
         end loop;
         return True;
      end if;
   end "=";

end Bounded_Stacks;
