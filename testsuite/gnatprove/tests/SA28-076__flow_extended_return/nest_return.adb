package body Nest_Return is

   procedure Nested_Proc (X : in Boolean; Y : out Boolean) is
   begin
      if X then
         Y := X;
         return;
      end if;
      Y := False;
   end Nested_Proc;

   function Nesting_Func (X : Boolean) return Boolean is
      Temp : Boolean;
   begin
      return Z : constant Boolean := X do
         case X is
            when True =>
               Nested_Proc (X, Temp);
               case Temp is
                  when True =>
                     null;
                  when False =>
                     return;
               end case;
            when others =>
               return;
         end case;
      end return;
   end Nesting_Func;

   function Declare_Block_Func (X : Boolean) return Boolean is
   begin
      return Z : constant Boolean := X do
         case X is
            when True =>
               declare
                  Temp : Boolean;
                  procedure Return_Proc (A : Boolean; B : out Boolean) is
                  begin
                     if A then
                        B := A;
                        return;
                     end if;
                     B := False;
                  end Return_Proc;
               begin
                  Return_Proc (X, Temp);
                  case Temp is
                     when True =>
                        null;
                     when False =>
                        return;
                  end case;
               end;
            when others =>
               return;
         end case;
      end return;
   end Declare_Block_Func;

end Nest_Return;
