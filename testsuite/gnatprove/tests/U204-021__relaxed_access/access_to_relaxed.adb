with Ada.Unchecked_Deallocation;

procedure Access_To_Relaxed with SPARK_Mode is
   type Pos_Access is access Positive;
   procedure Free_Pos is new Ada.Unchecked_Deallocation (Positive, Pos_Access);
   type Relaxed_Character is new Character with Relaxed_Initialization;
   type Pair is record
      Key : Relaxed_Character;
      Val : Pos_Access := null;
   end record;
   type Pair_Array is array (Positive range <>) of Pair;
   type Stack (Max : Natural) is record
      Content : Pair_Array (1 .. Max);
      Top     : Natural := 0;
   end record with
     Predicate => Top in 0 .. Max
     and (for all I in Content'Range =>
            (if I <= Top then Content (I).Key'Initialized
             else Content (I).Val = null));
   type Stack_Access is access Stack;
   procedure Free_Stack is new Ada.Unchecked_Deallocation (Stack, Stack_Access);

   function Size (S : Stack_Access) return Natural is
     (if S = null then 0 else S.Top);

   procedure Free_All (S : in out Stack_Access) with
     Post => Size (S) = 0
   is
   begin
      if S = null then
         return;
      end if;

      for I in 1 .. S.Top loop
         Free_Pos (S.Content (I).Val);
         pragma Loop_Invariant
           (for all K in 1 .. I => S.Content (K).Val = null);
      end loop;
      Free_Stack (S);
   end Free_All;

   procedure Push (S : in out Stack_Access; K : Character; V : Positive; Max : Natural) with
     Pre => Size (S) < Max
   is
   begin
      if S = null then
         declare
            Content : Pair_Array (1 .. 100);
         begin
            S := new Stack'(Max => 100, Content => Content, Top => 0);
         end;
      elsif S.Top = S.Max and Max > S.Max then
         declare
            Content : Pair_Array (1 .. Max);
            Top     : constant Natural := S.Top;
         begin
            Content (1 .. S.Max) := S.Content;
            Free_Stack (S);
            S := new Stack'(Max => Max, Content => Content, Top => Top);
         end;
      end if;

      S.Content (S.Top + 1).Key := Relaxed_Character (K);
      S.Top := S.Top + 1;
      S.Content (S.Top).Val := new Integer'(V);
   end Push;

   procedure Pop (S : in out Stack_Access; K : out Character; V : out Natural) with
     Pre => Size (S) > 0
   is
   begin
      K := Character (S.Content (S.Top).Key);
      if S.Content (S.Top).Val = null then
         V := 0;
      else
         V := S.Content (S.Top).Val.all;
         Free_Pos (S.Content (S.Top).Val);
      end if;
      S.Top := S.Top - 1;
   end Pop;

begin
   null;
end Access_To_Relaxed;
