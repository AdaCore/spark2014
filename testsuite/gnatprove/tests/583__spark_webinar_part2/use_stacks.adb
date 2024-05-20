with Types; use Types;
with Stacks; use Stacks;

procedure Use_Stacks
  with SPARK_Mode
is
   S : Stack := Empty_Stack;
   E : Element;

   function Is_Prime (X : Positive) return Boolean is
      (X = 2 or else (for all V in 2 .. X-1 => X mod V /= 0));

begin
   if Is_Prime (5_039) then -- (7! - 1) is prime

      S.Push (1);
      S.Push (2);
      S.Push (3);

   end if;

   E := S.Pop;

end Use_Stacks;
