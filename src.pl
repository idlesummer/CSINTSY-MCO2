% Top-level entry into program: ?- solve(diagnose(X, Y), CF).
solve(Goal, CF) :-
    print_instructions,
    retractall(known(_,_)),
    solve(Goal, CF, [], 20).

% gives allowable responses to an exshell query
print_instructions :-
    nl,
    write('You will be asked a series of queries.'), nl,
    write('Your response must be either:'), nl,
    write('    a. A number between -100 and 100 representing'), nl,
    write('       your confidence in the truth of the query'), nl,
    write('    b. why'), nl,
    write('    c. what'), nl,
    write('    d. how(X), where X is a goal'), nl, nl.


% META-INTERPRETER
% solve(+, ?, +, +)

% Case 1: truth value of goal is already known
solve(Goal, CF, _, Threshold) :-
    known(Goal, CF), !,
    above_threshold(CF, Threshold).

% Case 2: negated goal
solve(not(Goal), CF, Rules, Threshold) :- !,
    negate(Threshold, New_threshold),
    solve(Goal, CF_goal, Rules, New_threshold),
    negate(CF_goal, CF).

% Case 3: conjunctive goals
solve((Goal1, Goal2), CF, Rules, Threshold) :- !,
    solve(Goal1, CF1, Rules, Threshold),
    above_threshold(CF1, Threshold),
    solve(Goal2, CF2, Rules, Threshold),
    above_threshold(CF2, Threshold),
    min(CF1, CF2, CF).

% Case 4: back chain on a rule in knowledge base
solve(Goal, CF, Rules, Threshold) :-
    rule((Goal :- (Premise)), CF_rule),
    solve(Premise, CF_premise, [rule((Goal :- Premise), CF_rule) | Rules], Threshold),
    rule_cf(CF_rule, CF_premise, CF),
    above_threshold(CF, Threshold).

% Case 5: fact assertion in knowledge base
solve(Goal, CF, _, Threshold) :-
    rule(Goal, CF),
    above_threshold(CF, Threshold).

% Case 6: ask user
solve(Goal, CF, Rules, Threshold) :-
    askable(Goal),
    askuser(Goal, CF, Rules), !,
    assert(known(Goal, CF)),
    above_threshold(CF, Threshold).


% HELPER FUNCTIONS

% Prunes goal if certainty gets too low
above_threshold(CF, T) :- T >= 0, CF >= T.
above_threshold(CF, T) :- T < 0, CF =< T.

% Negates a number
negate(Num, Negated_num) :-
    Negated_num is -Num.

% Returns the minimum of two numbers
min(X, Y, X) :- X =< Y.
min(X, Y, Y) :- Y < X.

% Gets the product of two certainty factor percentages
rule_cf(CF_rule, CF_premise, CF) :-
    CF is (CF_rule * CF_premise / 100).


% USER INPUT AND DISPLAY OUTPUT

% Writes out a query and reads the user’s Answer
askuser(Goal, CF, Rules) :-
    format('Query : ~w ? ', [Goal]),
    read(Ans),
    respond(Ans, Goal, CF, Rules).

% Calls if user response is a certainty factor
respond(CF, _, CF, _) :-
    number(CF),
    CF =< 100,
    CF >= -100.

% Calls if user response is why and if rule stack is not empty
respond(why, Goal, CF, [Rule | Rules]) :-
    nl,
    write_rule(Rule),
    askuser(Goal, CF, Rules).

% Calls if user response is why and if rule stack is empty
respond(why, Goal, CF, []) :-
    nl,
    write('Back to the top of the rule stack.'), nl,
    askuser(Goal, CF, []).

respond(what, Goal, CF, Rules) :-
    nl,
    rule(desc(Goal, Desc)),
    write(Desc), nl, nl,
    askuser(Goal, CF, Rules).

% Calls if user response is how(X) and X is known
respond(how(X), Goal, CF, Rules) :-
    build_proof(X, CF_X, Proof), nl, !,
    format('The goal ~w was concluded with certainty ~w.', [X, CF_X]), nl, nl,
    write( 'The proof of this is:'), nl,
    write_proof(Proof, 0), nl,
    askuser(Goal, CF, Rules).

% Calls if user response is how(X) and if goal X is not known
respond(how(X), Goal, CF, Rules) :-
    nl,
    format('The truth of ~w', [X]), nl,
    write( 'is not yet known.'), nl, nl,
    askuser(Goal, CF, Rules).

% Calls if user response is invalid
respond(_, Goal, CF, Rules) :-
    nl,
    write('Unrecognized response.'), nl, nl,
    askuser(Goal, CF, Rules).

% PROOF BUILDER
% build_proof(+, ?, ?)

% Case 1: goal is given by user
build_proof(Goal, CF, (Goal, CF :- given)) :-
    known(Goal, CF), !.

% Case 2: negated goal
build_proof(not(Goal), CF, not(Proof)) :-
    build_proof(Goal, CF_goal, Proof),
    negate(CF_goal, CF).

% Case 3: conjunctive goals
build_proof((Goal1, Goal2), CF, (Proof1, Proof2)) :-
    build_proof(Goal1, CF1, Proof1),
    build_proof(Goal2, CF2, Proof2),
    min(CF1, CF2, CF).

% Case 4: back chaining
build_proof(Goal, CF, (Goal, CF :- Proof)) :-
    rule((Goal :- Premise), CF_rule),
    build_proof(Premise, CF_premise, Proof),
    rule_cf(CF_rule, CF_premise, CF).

% Case 5: goal is a fact in the knowledge base
build_proof(Goal, CF, (Goal, CF :- fact)) :-
    rule(Goal, CF).


% MORE DISPLAY OUTPUT HELPERS

% Displays a proof of a rule
write_rule(rule((Goal :- (Premise)), CF)) :-
    write( 'I am trying to prove the following rule:'), nl,
    format('~w :-', [Goal]), nl,
    write_premise(Premise),
    format('    CF = ~w', [CF]), nl, nl.

write_rule(rule(Goal, CF)) :-
    write( 'I am trying to prove the following goal:'), nl,
    format('~w CF = ~w', [Goal, CF]), nl.

% Displays a rule's premises
write_premise((Premise1, Premise2)) :- !,
    write_premise(Premise1),
    write_premise(Premise2).

write_premise(not(Premise)) :- !,
    format('    not ~w', [Premise]), nl.

write_premise(Premise) :- !,
    format('    ~w', [Premise]), nl.

% Displays the proof tree using indents
% write_proof(+,+)
write_proof((Goal, CF :- given), Level) :-
    indent(Level),
    format('~w CF = ~w was given by the user', [Goal, CF]), nl, !.

write_proof((Goal, CF :- fact), Level) :-
    indent(Level),
    format('~w CF = ~w was a fact of knowledge base', [Goal, CF]), nl, !.

write_proof((Goal, CF :- Proof), Level) :-
    indent(Level),
    format('~w CF = ~w :-', [Goal, CF]), nl,
    New_level is Level + 4,
    write_proof(Proof, New_level), !.

write_proof(not(Proof), Level) :-
    indent(Level),
    write('not '),
    write_proof(Proof, 0), !.

write_proof((Proof1, Proof2), Level) :-
    write_proof(Proof1, Level),
    write_proof(Proof2, Level), !.

% Helper predicate for indentation display
indent(0).
indent(Level) :-
    write(' '),
    New_level is Level - 1,
    indent(New_level).


% KNOWLEDGE BASE RULES

% Top-level query entry point rule/2
rule((diagnose(X, Y) :- (disease(X), info(X, Y))), 100).

% disease/2 statements
rule((disease(tonsillitis) :- (
    fever,
    pain(throat),
    difficulty(swallowing),
    hoarseness,
    swollen(tonsils),
    red(tonsils),
    presence_of(exudates),
    bad_breath
    )), 100).

rule((disease(pharyngitis) :- (
    fever,
    sore(throat),
    difficulty(swallowing),
    hoarseness,
    swollen(lymph_nodes),
    dry_cough,
    runny_nose
    )), 100).

rule((disease(laryngitis) :- (
    dry_cough,
    discomfort(throat),
    feeling_of(lump_in_throat),
    mild_soreness,
    difficulty(speaking)
    )), 100).

rule((disease(croup) :- (
    stridor,
    hoarseness,
    difficulty(breathing),
    barking_cough,
    stuffy_nose,
    agitated_mood,
    wheezing
    )), 100).

rule((disease(epiglottitis) :- (
    swollen(epiglottis),
    sudden_onset,
    severe(sore(throat)),
    difficulty(swallowing),
    difficulty(breathing),
    excessive(drooling),
    hoarseness,
    high(fever)
    )), 100).

rule((disease(sinusitis) :- (
    stuffy_nose,
    headache,
    pain(facial),
    cold_symptoms,
    postnasal_drip,
    loss_of(smell),
    cough,
    sore(throat),
    fever,
    bad_breath
    )), 100).

rule((disease(sinusitis) :- (
    stuffy_nose,
    headache,
    pain(facial),
    cold_symptoms,
    postnasal_drip,
    loss_of(smell),
    cough,
    sore(throat),
    fatigue,
    bad_breath
    )), 100).

rule((disease(nasal_polyp) :- (
    stuffy_nose,
    runny_nose,
    postnasal_drip,
    reduced(sense_of_smell),
    feeling_of(pressure_in_face_or_sinuses),
    headache,
    itchy(eyes),
    snoring,
    presence_of(growths_in_nasal_cavity)
    )), 100).

rule((disease(allergic_rhinitis) :- (
    sneezing,
    runny_nose,
    itchy(nose),
    itchy(throat),
    reduced(sense_of_smell)
    )), 100).

rule((disease(hyperthyroidism) :- (
    swollen(neck_area),
    loss_of(weight),
    increased(appetite),
    increased(heart_rate),
    feeling_of(anxiety),
    sensitivity_to(heat),
    excessive(sweating),
    shaky_hands,
    fatigue,
    insomnia,
    irregular(menstrual_patterns),
    bulging_eyes
    )), 100).

rule((disease(hypothyroidism) :- (
    swollen(neck_area),
    increased(weight_gain),
    fatigue,
    sensitivity_to(cold),
    constipation,
    hoarseness,
    pain(muscle),
    memory_issues,
    dry_hair,
    irregular(menstrual_patterns)
    )), 100).

rule((disease(mumps) :- (
    fever,
    swollen(parotid_glands),
    pain(swollen_area),
    headache,
    pain(muscle),
    fatigue,
    pain(swallowing),
    pain(ear),
    not(sex(female)),
    pain(testicular) %removed abdominal pain
    )), 100).

rule((disease(mumps) :- (
    fever,
    swollen(parotid_glands),
    pain(swollen_area),
    headache,
    pain(muscle),
    fatigue,
    pain(swallowing),
    pain(ear),
    sex(female),
    pain(adbominal)
    )), 100).

rule((disease(parotitis) :- (
    swollen(parotid_glands),
    pain(affected_area),
    red(affected_area),
    warm(affected_area),
    fever,
    dry_mouth,
    discharge(submandibular_duct),
    pain(during_saliva_production)
    )), 100).

rule((disease(otitis_media) :- (
    fever,
    pain(ear),
    feeling_of(fullness_or_pressure_in_ear),
    stuffy_nose, %changed from nasal congestion
    discharge(ear),
    balance_problems
    )), 100).

rule((disease(otitis_externa) :- (
    fever,
    pain(ear),
    itchy(ear),
    swollen(ear_area),
    discharge(ear),
    loss_of(hearing),
    pain(jaw)
    )), 100).

rule((disease(cholesteatoma) :- (
    presence_of(cyst),
    loss_of(hearing),
    discharge(ear),
    pain(ear),
    tinnitus,
    dizziness,
    feeling_of(fullness_or_pressure_in_ear)
    )), 100).

rule((disease(unknown)), 100).


% info/2 statements --------------------------------
rule((info(pharyngitis, 'Special equipment: Hematology analyzer. Checks for CBC (complete blood count) blood test to check for the level of infection.')), 100).
rule((info(laryngitis, 'Special equipment: Rigid Video Laryngoscopy. Used for physical examination to see the soreness of the affected area. Must be noted that this is usually for checking for severe cases.')), 100).
rule((info(epiglottitis, 'Special equipment: Rigid Video Laryngoscopy. This one is more likely to use the special equipment to check the inflammed area around the epiglottis')), 100).
rule((info(sinusitis, 'Special Equipment: Anterior rhinoscopy (shining a light and physically checking out the front part of the nasal cavity. Nasal endoscopy, uses an endoscope (long thin rope with a camera attached), can check the entire nasal cavity for inflammation/soreness including the middle and end.')), 100).
rule((info(nasal_polyp, 'Special Equipment: Nasal endoscopy to visualize and see the actual growths (pale, teardrop-shaped or grape-like growths.')), 100).
rule((info(allergic_rhinitis, 'Special equipment: Rhinoscopy. Checks around nasal tribunate area.')), 100).
rule((info(hyperthyroidism, 'Special equipment: Chemiluminescent Immunoassay (CLIA) Systems. used to measure thyroid hormones and antibodies. Ultrasound (CT Scan) for visualizing the state of the thyrioid gland.')), 100).
rule((info(hypothyroidism, 'Special equipment: Chemiluminescent Immunoassay (CLIA) Systems. used to measure thyroid hormones and antibodies. Ultrasound (CT Scan) for visualizing the state of the thyrioid gland.')), 100).
rule((info(unknown, 'No disease matches the given symptoms.')), 100).
rule((info(_, 'No special equipment needed.')), 100).

% rule/1 and desc/2 statements
rule(desc(agitated_mood, 'Increased restlessness and agitation')).
rule(desc(bad_breath, 'Foul odor originating from the mouth.')).
rule(desc(balance_problems, 'Issues with balance and equilibrium')). % new
rule(desc(barking_cough, 'Distinctive, harsh cough that resembles the sound of a dog barking ')).
rule(desc(bulging_eyes, 'Protrusion or swelling of the eyeballs.')). % new
rule(desc(stuffy_nose, 'Nasal congestion and blockage.')).
rule(desc(cold_symptoms, 'Runny nose, stuffy nose, throat discomfort and irritation.')). % ------------------- CHANGE
rule(desc(constipation, 'Difficulty passing stools.')). % new
rule(desc(cough, 'Coughing as a symptom')).
rule(desc(difficulty(breathing), 'Labored or obstructed breathing')).
rule(desc(difficulty(speaking), 'Challenges in producing sound and speaking')).
rule(desc(difficulty(swallowing), 'Struggle and discomfort when trying to swallow')).
rule(desc(discomfort(throat), ' Pain and discomfort in the throat')).
rule(desc(discharge(ear), 'Discomfort and pain in the ear')). % replaced fluid_drainage_from_the_ear
rule(desc(discharge(submandibular_duct), 'Pus-like drainage emerging from the opening of the duct in the mouth.')). % Possible purulent discharge from the duct opening inside the mouth
rule(desc(dizziness, 'Severe and debilitating head pain')). % neww
rule(desc(dry_cough, 'Tickly or itchy throat and does not produce any phlegm.')).
rule(desc(dry_hair, 'Hair has dull, brittle texture that is prone to breakage and split ends.')).
rule(desc(dry_mouth, 'Decreased saliva production where mouth feels parched and uncomfortable.')). % new
rule(desc(excessive(drooling), 'Unintentional flow of saliva from the mouth.')).
rule(desc(excessive(sweating), 'Profuse and persistent sweating')).
rule(desc(fatigue, 'Persistent tiredness and weakness.')).
rule(desc(feeling_of(anxiety), 'Feelings of unease and restlessness')).
rule(desc(feeling_of(lump_in_throat), 'Sensation of a foreign object in the throat')).
rule(desc(feeling_of(pressure_in_face_or_sinuses), 'Discomfort and pressure in the face')).
rule(desc(feeling_of(fullness_or_pressure_in_ear), 'Pressure and feeling of fulness in the ears')). % new
rule(desc(sex(female), 'Females are individuals of the female sex in biological terms')).
rule(desc(fever, 'An increase in body temperature above 37.2°C under the arm.')).
rule(desc(headache, 'Severe and debilitating head paindescription')).
rule(desc(high(fever), 'Elevated body temperature')).
rule(desc(hoarseness, 'Changes in voice quality, often with a rough or strained sound')).
rule(desc(increased(appetite), 'Heightened hunger and food intake.')). % new
rule(desc(increased(heart_rate), 'Condition where the heart beats faster than normal, can be referred to as palpitations')). % new (palpitations)
rule(desc(increased(weight_gain), 'Rapid and effortless weight increase')). % new (easier weight gain)
rule(desc(itchy(ear), 'Ears that itch and are irritated')). % neww
rule(desc(itchy(eyes), 'Eyes that itch and are irritated')).
rule(desc(itchy(nose), 'Irritation and itching in the nasal area')).
rule(desc(itchy(throat), 'Throat irritation with itching')).
rule(desc(insomnia, 'Difficulty falling asleep or staying asleep')). % new
rule(desc(irregular(menstrual_patterns), 'Abnormalities in the menstrual cycle')). % new
rule(desc(loss_of(hearing), 'Reduced ability to hear (in chronic cases)')). % neww
rule(desc(loss_of(smell), 'Decreased or absent sense of smell')).
rule(desc(loss_of(weight), 'decrease and loss of body weight')).
rule(desc(memory_issues, 'Problems with memory and cognition')). % new
rule(desc(mild_soreness, 'Mild pain or discomfort in the throat')).
rule(desc(nasal_congestion, 'Nasal congestion and blockage')). % new
rule(desc(pain(affected_area), 'Discomfort within a specific area')).
rule(desc(pain(adbominal), 'Discomfort felt in the area between the chest and the pelvis')).
rule(desc(pain(during_saliva_production), 'Discomfort felt when the mouth is producing saliva.')).
rule(desc(pain(ear), 'Discomfort and pain in the ear')).
rule(desc(pain(facial), 'Discomfort and pressure in the face')).
rule(desc(pain(jaw), 'Discomfort and pain in the jaw')).
rule(desc(pain(muscle), 'Aching or discomfort in the muscles')).
rule(desc(pain(swollen_area), 'Discomfort in a specific swollen area')).
rule(desc(pain(swallowing), 'Discomfort and pain when swallowing or talking')).
rule(desc(pain(testicular), 'Pain in the testicles (in males after puberty)')).
rule(desc(pain(throat), 'Discomfort and irritation in the throat')).
rule(desc(postnasal_drip, 'Excess production of mucus that drips down the back of the throat')).
rule(desc(presence_of(cyst), 'growths/presence of growths: pearly-white color, sac-like, accumulation of debris (earwax, dead skin cells, etc)')).
rule(desc(presence_of(exudates), 'Pus or white/yellow patches on the tonsils.')).
rule(desc(presence_of(growths_in_nasal_cavity), 'Growth-like structures in the nasal passages.')).
rule(desc(red(affected_area), 'Affected area is red')). 
rule(desc(red(tonsils), 'Tonsils are red.')).
rule(desc(reduced(sense_of_smell), 'Diminished or absence of sense of smell')).
rule(desc(runny_nose, 'Discharge of watery or mucus-like fluid from the nasal passages.')).
rule(desc(severe(sore(throat)), 'Intense throat pain and discomfort.')).
rule(desc(sensitivity_to(heat), 'Heightened sensitivity to heat.')). 
rule(desc(sensitivity_to(cold), 'Heightened sensitivity to cold temperatures.')). 
rule(desc(shaky_hands, 'Trembling or shaking of the hands.')). 
rule(desc(sneezing, 'Repeated involuntary expulsions of air through the nose and mouth.')).
rule(desc(snoring, 'Loud breathing sounds during sleep.')).
rule(desc(sore(throat), 'Pain and discomfort in the throat.')).
rule(desc(stridor, 'High-pitched, wheezing sound during breathing.')).
rule(desc(stuffy_nose, 'Nasal congestion and blockage.')).
rule(desc(sudden_onset, 'Rapid and abrupt development of symptoms.')).
rule(desc(swollen(ear_area), 'Enlargement and tenderness of the ear and the area round it.')). 
rule(desc(swollen(epiglottis), ' Inflammation and enlargement of the tissue at the back of the throat near the base of the tongue.')).
rule(desc(swollen(lymph_nodes), 'Enlargement and tenderness of lymph nodes in the neck.')).
rule(desc(swollen(neck_area), 'Enlargement of the neck area')). 
rule(desc(swollen(parotid_glands), 'Enlargement of the jaw area')). 
rule(desc(swollen(tonsils), 'Enlarged tonsils that may be red and inflamed.')).
rule(desc(tinnitus, 'Ringing or other noises in one or both ears.')). 
rule(desc(warm(affected_area), 'Slight increase in temperature in the affected area.')). 
rule(desc(wheezing, 'Whistling sound during breathing.')).

% Determines if a premise is askable within the knowledge base
askable(agitated_mood).
askable(bad_breath).
askable(balance_problems). 
askable(barking_cough).
askable(bulging_eyes). 
askable(stuffy_nose).
askable(cold_symptoms). 
askable(constipation). 
askable(cough).
askable(difficulty(breathing)).
askable(difficulty(speaking)).
askable(difficulty(swallowing)).
askable(discomfort(throat)).
askable(discharge(ear)). 
askable(discharge(submandibular_duct)). 
askable(dizziness). 
askable(dry_cough).
askable(dry_hair).
askable(dry_mouth). 
askable(excessive(drooling)).
askable(excessive(sweating)).
askable(fatigue).
askable(feeling_of(anxiety)).
askable(feeling_of(lump_in_throat)).
askable(feeling_of(pressure_in_face_or_sinuses)).
askable(feeling_of(fullness_or_pressure_in_ear)). 
askable(sex(female)).
askable(fever).
askable(headache).
askable(high(fever)).
askable(hoarseness).
askable(increased(appetite)). 
askable(increased(heart_rate)). 
askable(increased(weight_gain)). 
askable(itchy(ear)). 
askable(itchy(eyes)).
askable(itchy(nose)).
askable(itchy(throat)).
askable(insomnia). 
askable(irregular(menstrual_patterns)). 
askable(loss_of(hearing)). 
askable(loss_of(smell)).
askable(loss_of(weight)).
askable(memory_issues). 
askable(mild_soreness).
askable(nasal_congestion). 
askable(pain(affected_area)).
askable(pain(adbominal)).
askable(pain(during_saliva_production)).
askable(pain(ear)).
askable(pain(facial)).
askable(pain(jaw)).
askable(pain(muscle)).
askable(pain(swollen_area)).
askable(pain(swallowing)).
askable(pain(testicular)).
askable(pain(throat)).
askable(postnasal_drip).
askable(presence_of(cyst)). 
askable(presence_of(exudates)).
askable(presence_of(growths_in_nasal_cavity)).
askable(red(affected_area)). 
askable(red(tonsils)).
askable(reduced(sense_of_smell)).
askable(runny_nose).
askable(severe(sore(throat))).
askable(sensitivity_to(heat)). 
askable(sensitivity_to(cold)). 
askable(shaky_hands). 
askable(sneezing).
askable(snoring).
askable(sore(throat)).
askable(stridor).
askable(stuffy_nose).
askable(sudden_onset).
askable(swollen(ear_area)). 
askable(swollen(epiglottis)).
askable(swollen(lymph_nodes)).
askable(swollen(neck_area)). 
askable(swollen(parotid_glands)). 
askable(swollen(tonsils)).
askable(tinnitus). 
askable(warm(affected_area)). 
askable(wheezing).
