package body Common is

   function Detects_Failure (E : Monitoring) return Boolean is
   begin
      return E.Failed;
   end Detects_Failure;

   function Is_Active (E : Monitoring) return Boolean is
   begin
      return E.Active;
   end Is_Active;

   function Activate (E : Monitoring) return Monitoring is
   begin
      return Monitoring'(Failed => E.Failed, Active => True);
   end Activate;

   function Weight (E : Monitoring) return Integer is
   begin
      if Is_Active(E) then
         return 1;
      else
         return 0;
      end if;
   end Weight;

   function "<" (Left, Right : Recovery) return Boolean is
   begin
      return Left.Priority < Right.Priority;
   end "<";

end Common;
