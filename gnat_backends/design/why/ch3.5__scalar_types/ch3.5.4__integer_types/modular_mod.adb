with Modular; use Modular;

function Modular_Mod (A : Integer) return Modular.Byte is
   M : Modular.Byte := Modular.Byte'Mod (A + 4);
begin
   return M;
end Modular_Mod;
