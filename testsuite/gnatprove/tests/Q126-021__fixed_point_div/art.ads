with TPS; pragma Elaborate_All (TPS);

package ART is

   Time_Unit : constant Duration :=
     Duration (1.0 / Float (Duration (TPS)));

end;
