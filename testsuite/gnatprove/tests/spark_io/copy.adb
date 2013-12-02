------------------------------------------------------------------------------
--                                                                          --
--                           SPARK_IO EXAMPLES                              --
--                                                                          --
--                     Copyright (C) 2013, Altran UK                        --
--                                                                          --
-- SPARK is free software;  you can redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

pragma SPARK_Mode (On);

with My_Files;                use My_Files;
with My_Number_IO;            use My_Number_IO;
with SPARK.Text_IO;           use SPARK.Text_IO;
with Ada.Characters.Handling; use Ada.Characters.Handling;

procedure Copy
  with Global  => (In_Out => (Source, Destination,
                              Standard_Input, Standard_Output,
                              Standard_Error)),
  Depends => ((Destination, Source) =>  (Source, Destination,
                                         Standard_Input, Standard_Output),
               Standard_Output      => +(Source, Destination, Standard_Input),
               Standard_Input       => +(Source, Destination, Standard_Output),
               Standard_Error       => +(Source, Destination,
                                         Standard_Output, Standard_Input)),
  Pre     => Status (Standard_Error) = Success and
             Is_Writable (Standard_Error) and
             not Is_Open (Source) and
             not Is_Open (Destination)
is
   Count : Count_Range;
   Count_Limit_Reached : Boolean;

   Response : String (1 .. 512);
   Yes_No   : String (1 .. 4);
   Yes : constant String := "YES";
   No  : constant String := "NO";
   Last,
   Last_Of_Yes_No : Natural;
   C : Character_Result;
begin
   Count := 0;
   Count_Limit_Reached := False;

   loop
      pragma Loop_Invariant (Status (Standard_Error) = Success and
                             Is_Writable (Standard_Error) and
                             not Is_Open (Source));
      if Status (Standard_Output) = Success then
         Put ("Please enter the source file name: ");
      else
         Put_Line (Standard_Error, "Unable to write to standard output.");
         return;
      end if;


      Get_Line (Item => Response,
                Last => Last);

      if Status (Standard_Input) = Success and
        Last >= Response'First and
        Last <= Response'Last
      then
         declare
            File_Name : String renames Response (Response'First .. Last);
         begin
            Open (The_File => Source,
                  The_Mode => In_File,
                  The_Name => File_Name);

            case Status (Source) is
               when Success => exit;
               when Name_Error =>
                  if Status (Standard_Output) = Success then
                     Put_Line ("Sorry, the file " & File_Name
                               & " does not exist.");
                  else
                     Put_Line (Standard_Error,
                               "Unable to write to standard output.");
                     return;
                  end if;
               when Use_Error =>
                  if Status (Standard_Output) = Success then
                     Put_Line ("Sorry, the file " & File_Name
                               & " is not accessible to you.");
                  else
                     Put_Line (Standard_Error,
                               "Unable to write to standard output.");
                     return;
                  end if;
               when others =>
                  if Status (Standard_Output) = Success then
                     Put_Line
                       ("Oh dear; an error in the file system has occured");
                  else
                     Put_Line (Standard_Error,
                               "Unable to write to standard output.");
                  end if;
                  return;
            end case;
         end;

      elsif Status (Standard_Input) /= Success then
         if Status (Standard_Output) = Success then
            Put_Line ("Oh dear; an error with the standard input has occured");
         else
            Put_Line (Standard_Error,
                      "Unable to write to standard output.");
         end if;
         return;
      end if;

   end loop;

   Dest : loop
      pragma Loop_Invariant (Status (Standard_Error) = Success and
                             Is_Writable (Standard_Error) and
                             not Is_Open (Destination) and
                             Is_Open (Source) and
                             not Is_Standard_File (Source) and
                             Is_Readable (Source));
      if Status (Standard_Output) = Success then
         Put ("Please enter the Destination file name: ");
      else
         Put_Line (Standard_Error,
                   "Unable to write to standard output.");
         return;
      end if;

      Get_Line (Item => Response,
                Last => Last);

      if Status (Standard_Input) = Success and
        Last >= Response'First and Last <= Response'Last
      then
         declare
            File_Name : String renames Response (Response'First .. Last);
         begin
            Create (The_File => Destination,
                    The_Mode => Out_File,
                    The_Name => File_Name);

            case Status (Destination) is
               when Success => exit Dest;
               when Name_Error =>
                  if Status (Standard_Output) = Success then
                     Put_Line ("Sorry, invalid file name"
                               & File_Name);
                  else
                     Put_Line (Standard_Error,
                               "Unable to write to standard output.");
                     return;
                  end if;
               when Use_Error =>
                  if Status (Standard_Output) = Success then
                     Put_Line ("Sorry, invalid file name"
                               & File_Name);
                  else
                     Put_Line (Standard_Error,
                             "Unable to write to standard output.");
                     return;
                  end if;
                  if Status (Standard_Output) = Success then
                     Put_Line ("The file " & File_Name
                               & " already extits.");
                  end if;
                  if Status (Standard_Output) = Success then
                     Put_Line ("Do you want to overwrite it? (Yes/No)");
                  else
                     Put_Line (Standard_Error,
                               "Unable to write to standard output.");
                     return;
                  end if;

               Overwrite : loop
                     pragma Loop_Invariant (not Is_Open (Destination) and
                                            Status (Standard_Error) = Success
                                            and Is_Writable (Standard_Error));
                  Get_Line (Item => Yes_No,
                            Last => Last_Of_Yes_No);
                  if Status (Standard_Input) = Success then
                     declare
                        Length_Of_Yes_No : constant Natural :=
                        Last_Of_Yes_No - Yes_No'First + 1;
                     begin
                        if Length_Of_Yes_No > 0 and Length_Of_Yes_No <= 3 then
                           if Length_Of_Yes_No < 3 and then
                             No (1 .. Length_Of_Yes_No) = To_Upper
                             (Yes_No (Yes_No'First .. Last_Of_Yes_No))
                           then
                              exit Overwrite;
                           elsif Yes (1 .. Length_Of_Yes_No) = To_Upper
                             (Yes_No (Yes_No'First .. Last_Of_Yes_No))
                           then
                              Open (The_File => Destination,
                                    The_Mode => Out_File,
                                    The_Name => File_Name
                                   );
                              if Status (Destination) = Success then
                                 exit Dest;
                              elsif Status (Standard_Output) = Success then
                                 Put_Line ("Sorry, unable to overwrite "
                                          & File_Name);
                                 exit Overwrite;
                              else
                                 Put_Line
                                   (Standard_Error,
                                    "Unable to write to standard output.");
                                 return;
                              end if;
                           end if;
                        end if;
                           if Status (Standard_Output) = Success then
                              Put ("Please enter Yes or No: ");
                           else
                              Put_Line (Standard_Error,
                                   "Unable to write to standard output.");
                              return;
                           end if;
                     end;
                  end if;
               end loop Overwrite;
               when others =>
                  if Status (Standard_Output) = Success then
                     Put_Line
                       ("Oh dear; an error in the file system has occured");
                  else
                     Put_Line (Standard_Error,
                               "Unable to write to standard output.");
                  end if;
                  Close (Source);
                  return;
            end case;
         end;

      elsif Status (Standard_Input) /= Success then
         if Status (Standard_Output) = Success then
            Put_Line
              ("Oh dear; an error with the standard input has occured");
         else
            Put_Line (Standard_Error,
                      "Unable to write to standard output.");
         end if;
         Close (Source);
         return;
      end if;

   end loop Dest;


   while not End_Of_File (Source) loop
      pragma Loop_Invariant (Status (Standard_Error) = Success and
                             Is_Writable (Standard_Error) and
                             Is_Open (Source) and
                             Is_Open (Destination) and
                             Is_Readable (Source) and
                             Is_Writable (Destination) and
                             not Is_Standard_File (Source) and
                             not Is_Standard_File (Destination));
      Get (Source, C);
      if C.Status = Success then
         if Status (Destination) = Success then
            Put (Destination, C.Item);
            if not Count_Limit_Reached then
               if Count < Count_Range'Last then
                  Count := Count + 1;
               else
                  Count_Limit_Reached := True;
               end if;
            end if;
         else
            if Status (Standard_Output) = Success then
               Put_Line
                 ("Oh dear, a file error has occured while writing to " &
                  Name (Destination));
               exit;
            else
               Put_Line (Standard_Error,
                  "Unable to write to standard output.");
               Close (Source);
               Close (Destination);
               return;
            end if;
         end if;
      else
         if Status (Standard_Output) = Success then
            Put_Line ("An error has occured reading " &
                      Name (Source));
            exit;
         else
            Put_Line (Standard_Error,
              "Unable to write to standard output.");
            Close (Source);
            Close (Destination);
            return;
         end if;
      end if;
   end loop;

   if not Count_Limit_Reached then
      if Status (Standard_Output) = Success then
         Put (Count);
      end if;
      if Status (Standard_Output) = Success then
         Put_Line (" characters copied.");
      end if;
   else
      if Status (Standard_Output) = Success then
         Put ("More than ");
      end if;

      if Status (Standard_Output) = Success then
         Put (Count_Range'Last);
      end if;

      if Status (Standard_Output) = Success then
         Put_Line (" characters copied.");
      end if;
   end if;

   if Status (Standard_Output) = Success then
      Put_Line ("Closing all files.");
   end if;
   if Is_Open (Source) then
      Close (Source);
   end if;

   if Is_Open (Destination) then
      Close (Destination);
   end if;
end Copy;
