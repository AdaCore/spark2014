with Ada.Text_Io;
use Ada.Text_Io;

procedure Evoting_Simple is
   subtype Name is String (1 .. 80);

   type Counter_Range_t is new Integer range 0..10_000;
   type Candidate_Number_t is range 0..20;
   type Total_Range_t is
     new Integer range
       0..(Integer(Counter_Range_t'Last) * Integer(Candidate_Number_t'Last));
   type Candidate_Name_Array_t is array (Candidate_Number_t) of Name;
   type Counters_t is array (Candidate_Number_t) of Counter_Range_t;

   CANDIDATES_FILENAME : constant String := "candidates.txt";

   procedure Read_Candidates(candidates : out Candidate_Name_Array_t;
                             num_candidates : out Candidate_Number_t) is
      file : File_Type;
      current_candidate : Candidate_Number_t := 1;
      last : Natural;
      item : Name;
   begin
      item (1 .. 7) := "No vote";
      candidates(candidates'First) := item;
      Open(File => file, Mode => In_File, Name => CANDIDATES_FILENAME);

      while not(End_Of_File(file))
            and current_candidate <= candidates'Last loop
         Get_Line(File => file, Item => item, Last => last);
         candidates(current_candidate) := item(1..last);
         current_candidate := current_candidate + 1;
      end loop;

      Close(file);
      num_candidates := current_candidate - 1;
      return;
   end Read_Candidates;

   procedure Print_A_Candidate(candidates : Candidate_Name_Array_t;
                               candidate_id : Candidate_Number_t) is
   begin
         Put(Candidate_Number_t'Image(candidate_id));
         Put(". ");
         Put(candidates(candidate_id));
   end Print_A_Candidate;

   procedure Print_Candidates(candidates : Candidate_Name_Array_t;
                              num_candidates : in Candidate_Number_t) is
   begin
      for i in 0..num_candidates loop
         Put("    ");
         Print_A_Candidate(candidates, i);
         Put_Line("");
      end loop;
   end Print_Candidates;

   procedure Vote_Setup(candidates : out Candidate_Name_Array_t;
                        num_candidates : out Candidate_Number_t) is
   begin
      Put_Line("**** Vote Setup ****");
      Put("* reading candidates file '");
      Put(CANDIDATES_FILENAME);
      Put_Line("'");

      Read_Candidates(candidates, num_candidates);

      Put(Candidate_Number_t'Image(num_candidates));
      Put_Line(" candidates:");
      Print_Candidates(candidates, num_candidates);
      return;
   end Vote_Setup;

   procedure Get_Vote(candidates : Candidate_Name_Array_t;
                      num_candidates : Candidate_Number_t;
                      chosen_vote : out Candidate_Number_t) is
      buf : String(1..10);
      last : Natural;
      choice : Candidate_Number_t;
   begin
      loop
         Put_Line("Chose a candidate:");
         Print_Candidates(candidates, num_candidates);
         Put("Your choice (0-");
         Put(Candidate_Number_t'Image(num_candidates));
         Put_Line(")");

         Get_Line(buf, last);
         choice := Candidate_Number_t'Value(buf(1..last));
         if choice >= 0 and choice <= num_candidates then
            Put("Are you sure your vote ");
            Print_A_Candidate(candidates, choice);
            Put_Line(" is correct (y/n)?");

            Get_Line(buf, last);
            if buf(1) = 'y' or buf(1) = 'Y' then
               chosen_vote := choice;
               return;
            else
               Put_Line("Vote canceled, redo");
            end if;
         else
            Put("Invalid choice (");
            Put(Candidate_Number_t'Image(choice));
            Put_Line("), redo");
         end if;
      end loop;
   end Get_Vote;

   procedure Voting(candidates : in Candidate_Name_Array_t;
                    num_candidates : in Candidate_Number_t;
                    counters : in out Counters_t;
                    number_of_votes : in out Natural) is
      buf : String(1..255);
      last : Natural;
      chosen_vote : Candidate_Number_t;
   begin
      Put_Line("**** Voting ****");

      while number_of_votes < Natural(num_candidates * Counters_t'Last) loop
         Put_Line("Do you want to vote or stop the vote (v/'end of vote')?");
         Get_Line(Item => buf, Last => last);
         if buf(1) = 'v' then
            Get_Vote(candidates, num_candidates, chosen_vote);

            if counters(chosen_vote) < Counter_Range_t'Last then
               counters(chosen_vote) := counters(chosen_vote) + 1;
               number_of_votes := number_of_votes + 1;
               Put("Vote stored: ");
               Print_A_Candidate(candidates, chosen_vote);
               Put_Line("");
            else
               return;
            end if;

         elsif buf(1..11) = "end of vote" then
            return;
         end if;
      end loop;
   end Voting;

   procedure Compute_Winner(num_candidates : in Candidate_Number_t;
                            counters : in Counters_t;
                            winner : out Candidate_Number_t) is
   begin
      winner := 1; -- "No vote" is NOT taken into account
      for i in 2..num_candidates loop
         if counters(i) > counters(winner) then
            winner := i;
         end if;
      end loop;
   end Compute_Winner;

   procedure Compute_Results(candidates : in Candidate_Name_Array_t;
                             num_candidates : in Candidate_Number_t;
                             counters : in Counters_t) is
      total : Total_Range_t := 0;
      valid_total : Total_Range_t; -- votes different from "No vote"
      winner : Candidate_Number_t;
   begin
      Put_Line("**** Result ****");

      for i in 0..num_candidates loop
         total := total + Total_Range_t(counters(i));
      end loop;

      valid_total := total - Total_Range_t(counters(0));

      for i in 0..num_candidates loop
         Put(Counter_Range_t'Image(counters(i)));
         Put(" vote(s): ");
         Print_A_Candidate(candidates, i);
         Put_Line("");
      end loop;

      Put("Total number of votes: ");
      Put(Total_Range_t'Image(total));
      Put_Line("");

      Put("Total number of valid votes: ");
      Put(Total_Range_t'Image(valid_total));
      Put_Line("");

      Compute_Winner(num_candidates, counters, winner);
      Put("* Winner ");
      Print_A_Candidate(candidates, winner);
      Put_Line("");
   end Compute_Results;

   candidates : Candidate_Name_Array_t; -- := (others => "--undefined--");
   counters : Counters_t := (others => 0);
   num_candidates : Candidate_Number_t := 0;
   number_of_votes : Natural := 0;

begin
   Put_Line("**** Start of evoting program (Ada version) ****");

   Vote_Setup(candidates, num_candidates);

   Voting(candidates, num_candidates, counters, number_of_votes);

   Compute_Results(candidates, num_candidates, counters);
end Evoting_Simple;

