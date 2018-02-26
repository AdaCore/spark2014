package body Stacks with SPARK_Mode is

   procedure Reset (S : in out Stack) is
   begin
      S.Length := 0;
   end Reset;

   procedure Pop (S : in out Stack; E : out Element) is
   begin
      E := S.Content (S.Length);
      S.Length := S.Length - 1;
   end Pop;

   procedure Push (S : in out Stack; E : Element) is
   begin
      S.Length := S.Length + 1;
      S.Content (S.Length) := E;
   end Push;

   procedure Reset (S : in out Buffer) is
   begin
      S.First := 1;
      S.Length := 0;
   end Reset;

   procedure Pop (S : in out Buffer; E : out Element) is
   begin
      E := S.Content (Last (S));
      S.Length := S.Length - 1;
   end Pop;

   procedure Push (S : in out Buffer; E : Element) is
   begin
      S.Length := S.Length + 1;
      S.Content (Last (S)) := E;
   end Push;

   procedure Enqueue (S : in out Buffer; E : Element) is
   begin
      S.Length := S.Length + 1;
      if S.First = 1 then
         S.First := Max;
      else
         S.First := S.First - 1;
      end if;
      S.Content (S.First) := E;
   end Enqueue;
end Stacks;
