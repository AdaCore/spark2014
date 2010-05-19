-- Maths functions on system types
--
-- $Log: systemtypes-maths.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/07 19:18:59  adi
-- Initial revision
--
--
package body SystemTypes.maths is

   function Top_Bit(I : Systemtypes.Integer32)
                   return Systemtypes.Integer32
   is
      Ans : Systemtypes.Integer32;
   begin
      Ans := 1;
      while Ans < I loop
         --# assert ans >= 1;
         Ans := Ans * 2;
      end loop;
      return Ans;
   end Top_Bit;

   -- Integer square root
   --
   function Sqrt(I : Systemtypes.Integer32)
                return Systemtypes.Integer32
   is
      E,E_Sq,
        D_E,
        E_P1_Sq,
        tmp
        : Systemtypes.Integer32;
   begin
      -- Set are
      E_sq := Top_Bit(I);
      E := E_Sq / 2;
      D_E := E / 2;
      E_P1_Sq := E_Sq + (2*E + 1);
      while D_E > 0 and
        not (E_Sq <= I and E_P1_Sq > I) loop
         --# assert d_e > 0;
         -- Try increasing E by D_e
         Tmp := E_Sq + ((2*(E*D_E)) + (D_E*D_E));
         if Tmp > I then
            -- Too high, do nothing to E
            D_E := D_E / 2;
         else
            E := E + D_E;
            E_Sq := E*e;
            E_P1_Sq := E_Sq + (2*E + 1);
            D_E := D_E / 2;
         end if;
      end loop;
      return e;
   end Sqrt;


end SystemTypes.Maths;
