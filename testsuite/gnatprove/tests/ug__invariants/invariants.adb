package body Invariants with SPARK_Mode is

   procedure Push_Internal (S : in out Stack; E : Element) with
     Pre  => S.Size < My_Length'Last,
     Post => S.Size = S.Size'Old + 1 and S.Content (S.Size) = E
     and S.Content (1 .. S.Size)'Old = S.Content (1 .. S.Size - 1)
     and S.Max = S.Max'Old
   is
   begin
      S.Size := S.Size + 1;
      S.Content (S.Size) := E;
   end Push_Internal;

   procedure Push (S : in out Stack; E : Element) is
   begin
      Push_Internal (S, E);
      if S.Max < E then
         S.Max := E;
      end if;
   end Push;

   procedure Push_Zero (S : in out Stack) is
   begin
      Push (S, 0);
   end Push_Zero;

   The_Stack : Stack := (Content => (others => 1),
                         Size    => 5,
                         Max     => 0);

   function Size return My_Length is (The_Stack.Size);

   procedure Push_Internal (E : Element) with
     Pre  => The_Stack.Size < My_Length'Last
   is
   begin
      The_Stack.Size := The_Stack.Size + 1;
      The_Stack.Content (The_Stack.Size) := E;
   end Push_Internal;

   procedure Push (E : Element) is
   begin
      Push_Internal (E);
      if The_Stack.Max < E then
         The_Stack.Max := E;
      end if;
   end Push;

   procedure Push_Zero is
   begin
      Push (0);
   end Push_Zero;

begin
   The_Stack.Max := 1;
end Invariants;
