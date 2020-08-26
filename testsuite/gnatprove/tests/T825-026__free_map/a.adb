with Ada.Unchecked_Deallocation;
package body A with SPARK_Mode is
    procedure Free_Mem (S : in out Structure)
    is
--       procedure Free_Map(M : in out Map_Acc)
--         with
--           Import => True,
--           Depends => (M => null, null => M),
--           Post => M = null;
       procedure Free_Map is new Ada.Unchecked_Deallocation (Object => Map, Name => Map_Acc);

       M : Map_Acc := S.Map_field;
    begin
       while M /= null loop
          declare
             Next_M : Map_Acc := M.Next;
          begin
             M.Next := null;
             Free_Map(M);
             M := Next_M;
          end;
       end loop;
       S.Map_field := null;
    end Free_Mem;
end A;
