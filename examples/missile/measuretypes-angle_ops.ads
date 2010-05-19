-- Options for measuring physical phenomena
--
-- $Log: measuretypes-angle_ops.ads,v $
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/25 14:05:36  adi
-- Added Mul operation
--
-- Revision 1.1  2003/08/08 19:14:58  adi
-- Initial revision
--
--

with Systemtypes;
--# inherit Measuretypes,systemtypes;
package Measuretypes.Angle_Ops is

   function Sum(Left, Right : Measuretypes.Millirad)
               return Measuretypes.Millirad;
   function Mul(Orig_Angle : Measuretypes.Millirad;
                Mult       : Integer)
     return Measuretypes.Millirad;
   function Diff(Left, Right : Measuretypes.Millirad)
                return Measuretypes.Millirad;
   function Negate(Orig_Angle : Measuretypes.Millirad)
                  return Measuretypes.Millirad;
   function Create_Angle(Word : Systemtypes.Word)
                        return Measuretypes.Millirad;
   function Millirad_To_Word(Orig_Angle : Measuretypes.Millirad)
                            return Systemtypes.Word;
   function Int_To_Millirad(Count : in Systemtypes.Integer32)
                           return Measuretypes.Millirad;
   function Round_Degree(Orig_Angle : Measuretypes.Millirad)
                        return Measuretypes.Angle_Degrees;
   function Degree_To_Millirad(Orig_Degree : Measuretypes.Angle_Degrees)
                              return Measuretypes.Millirad;

end Measuretypes.Angle_Ops;
