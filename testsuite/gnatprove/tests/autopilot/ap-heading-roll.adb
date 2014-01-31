with Instruments,Degrees,Surfaces,Scale;
use type Instruments.Headdegree,
  Instruments.Bankangle,
  Instruments.Machnumber;

with AP.Heading.Roll.Rate;

use type Degrees.Degreespersec;
use type Surfaces.Controlangle;

package body AP.Heading.Roll
  with Refined_State => (State => AP.Heading.Roll.Rate.Roll_History)
is
   procedure Calc_Rollrate(Roll : in Instruments.Bankangle;
			   Present_Rollrate : out Degrees.Degreespersec)
                          renames Rate.Calc_Rollrate;

   subtype Degreespersec is Degrees.Degreespersec;

   function Target_ROR(Present_Heading : Instruments.Headdegree;
		       Target_Heading  : Instruments.Headdegree)
		      return Instruments.Bankangle
   is
      Result : Instruments.Bankangle;
      Offset : Instruments.Headdegree;
   begin
      Offset := Scale.Heading_Offset(Present_Heading,Target_Heading);
      if Offset > 40 and Offset <= 180 then
         Result := 40;
      elsif Offset > 180 and Offset < 320 then
         Result := -40;
      elsif Offset <= 40 then
         Result := Instruments.BankAngle(Offset);
      else
         Result := Instruments.BankAngle(360 - Integer(Offset));
      end if;
      return Result;
   end Target_ROR;

   function Target_Rate(Present_Heading : Instruments.Headdegree;
			Target_Heading  : Instruments.Headdegree;
			Bank            : Instruments.Bankangle)
		       return Degreespersec
   is
      Target_Bank : Instruments.Bankangle;
      Result : Degreespersec;
   begin
      Target_Bank := Target_ROR(Present_Heading,Target_Heading);
      Result := Degreespersec( (Target_Bank - Bank) / 5 );
      if Result > 10 then
         Result := 10;
      elsif Result < -10 then
         Result := -10;
      end if;
      return Result;
   end Target_Rate;


   function Calc_Aileron_Move(Present_Bank : Degreespersec;
			      Target_Bank  : Degreespersec;
			      Mach : Instruments.Machnumber)
			     return Surfaces.Controlangle
   is
      Target_Angle : Surfaces.ControlAngle;
   begin
      Target_Angle := Scale.Scale_Movement(
	Mach    => Mach,
	Present => Scale.Scaledata(Present_Bank / 2),
	Target  => Scale.Scaledata(Target_Bank / 2),
	Max     => Surfaces.ControlAngle(40)
      );
      return Target_Angle;
   end Calc_Aileron_Move;


   procedure Roll_AP(Mach            : in Instruments.Machnumber;
		     Present_Heading : in Instruments.Headdegree;
		     Target_Heading  : in Instruments.Headdegree;
		     Bank            : in Instruments.Bankangle)
     with Refined_Global  => (Output => Surfaces.Ailerons,
                              In_Out => Rate.Roll_History),
          Refined_Depends => (Rate.Roll_History =>+ Bank,
                              Surfaces.Ailerons => (Bank,
                                                    Mach,
                                                    Present_Heading,
                                                    Rate.Roll_History,
                                                    Target_Heading))
   is
      Present_Rollrate : Degreespersec;
      Target_Rollrate  : Degreespersec;
      Aileron_Movement : Surfaces.Controlangle;
   begin
      Calc_Rollrate(Bank,Present_Rollrate);
      Target_Rollrate := Target_Rate(Present_Heading,
                                     Target_Heading,
                                     Bank);
      Aileron_Movement := Calc_Aileron_Move(Present_Rollrate,
                                            Target_Rollrate,
                                            Mach);
      Surfaces.Move_Ailerons(Aileron_Movement);
   end Roll_AP;

end AP.Heading.Roll;
