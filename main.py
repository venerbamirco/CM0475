# definitions:

# definition element in CA
# (ra, Rp, Rn,rt) ∈ CA has the following meaning: users with administrative role ra can assign role rt to
# any user who has all the roles in Rp and none of the roles in Rn

# definition element in CR
# (ra,rt) ∈ CR has the following meaning:
# users with administrative role ra can revoke role rt from any user.

# function used to create the parser of the input file
def parser_file ( file_name ) :
    # store the number of actual line
    count = 0
    # store the set of all roles
    roles = [ ]
    # store the set of all users
    users = [ ]
    # store the set of all user roles
    user_roles = [ ]
    # store the set of all can revoke rules
    can_revoke_rules = [ ]
    # store the set of all can assign rules
    can_assign_rules = [ ]
    # store the state goal
    goal = ""
    # for each row in the file
    for line in open ( file_name , "r" ).readlines ( ) :
        # i check even row because odd rows are empty lines
        # alternatively i can check the first word in the row and then see if it is a can assign , a can revoke, a user, a role etc.
        # if it is the row of roles
        if count == 0 :
            roles = line.split ( " " ) [ 1 : -1 ]  # roles from the input file - line 0 - no word roles and no semicolon
        # if it is the row of users
        elif count == 2 :
            users = line.split ( " " ) [ 1 : -1 ]  # users from the input file - line 2 - no word users and no semicolon
        # if it is the row of user roles
        elif count == 4 :
            first_split = line.split ( " " ) [ 1 : -1 ]  # UA from the input file - line 4 - no word UA and no semicolon
            for fp in first_split :
                tuple = fp.split ( "," )
                user_roles.append ( [ tuple [ 0 ] [ 1 : ] , tuple [ 1 ] [ :-1 ] ] )
        # if it is the row of can revoke rules
        elif count == 6 :
            first_split = line.split ( " " ) [ 1 : -1 ]  # CR from the input file - line 6 - no word CR and no semicolon
            for fp in first_split :
                tuple = fp.split ( "," )
                can_revoke_rules.append ( [ tuple [ 0 ] [ 1 : ] , tuple [ 1 ] [ :-1 ] ] )
        # if it is the row of can assign rules
        elif count == 8 :
            first_split = line.split ( " " ) [ 1 : -1 ]  # CA from the input file - line 8 - no word CA and no semicolon
            for fp in first_split :
                tuple = fp.split ( "," )
                if tuple [ 1 ] == "TRUE" :
                    can_assign_rules.append ( [ tuple [ 0 ] [ 1 : ] , [ ] , [ ] , tuple [ 2 ] [ :-1 ] ] )  # CA without < and >
                else :
                    yes_can_assign_rules = [ ]
                    no_can_assign_rules = [ ]
                    second_split = tuple [ 1 ].split ( "&" )  # get all role parts in the CA definitions
                    for sp in second_split :
                        if sp [ 0 ] == '-' :  # if not actual role
                            no_can_assign_rules.append ( sp [ 1 : ] )
                        else :  # if yes actual role
                            yes_can_assign_rules.append ( sp )
                    can_assign_rules.append ( [ tuple [ 0 ] [ 1 : ] , yes_can_assign_rules , no_can_assign_rules , tuple [ 2 ] [ :-1 ] ] )
        # if it is the row of goal
        elif count == 10 :
            goal = line.split ( " " ) [ 1 ]
        # increment counter to get the correct row parser
        count += 1
    # return all parts of the input file
    return roles , users , user_roles , can_revoke_rules , can_assign_rules , goal

# function used to construct the model of the list of all roles for each user
def model_users_roles ( user_roles ) :
    # using the checkable_user_role create a structure as [['user0', ['Admin']], ['user1', ['Doctor']]...] where each user has the list of his roles
    roles_each_user = [ ]
    # for each user
    for u in users :
        # initialize his roles as empty list
        roles = [ ]
        # for each user role in the input parameter
        for user_role in user_roles :
            # if the actual user has the actual role
            if u == user_role [ 0 ] :
                # save the actual role to the list of roles of the actual user
                roles.append ( user_role [ 1 ] )
        # save the actual user with his roles
        roles_each_user.append ( [ u , roles ] )
    # transfrom [['user0', ['Admin']], ['user1', ['Doctor']]...] to {'user0': ['Admin'], 'user1': ['Doctor']....} because is more simpler the intersection using only &
    roles_each_user = { x [ 0 ] : x [ 1 : ] [ 0 ] for x in roles_each_user }
    return roles_each_user

# backward slicing definition
# S0 = {rg}
# Si = Si−1 ∪ {Rp ∪ Rn ∪ {ra} | (ra, Rp, Rn,rt) ∈ CA ∧ rt ∈ Si−1}
# Let S∗ be the fixed point to this set of equations, then:
# 1 remove from CA all the rules that assign a role in R \ S∗
# 2 remove from CR all the rules that revoke a role in R \ S∗
# 3 delete the roles in R \ S∗

# function used to calculate the backward slicing
def backward_slicing ( goal , can_assign_rules , can_revoke_rules ) :
    # s0={rg}
    previous_state = [ goal ]
    next_state = [ ]
    fixed_point_reached = False
    # the procedure works by repeating until a fixed point is reached
    while not fixed_point_reached :
        # Si = Si−1 ∪...
        next_state = previous_state
        # condition (ra, Rp, Rn,rt) ∈ CA
        for can_assign_rule in can_assign_rules :
            # can assign rule example ['Admin', ['PrimaryDoctor', 'Manager'], [], 'target']
            # condition rt ∈ Si−1
            if can_assign_rule [ -1 ] in previous_state :
                # Si = Si−1 ∪ {Rp ∪ Rn ∪ {ra}} using structure (ra, Rp, Rn,rt) ∈ CA
                for rp in can_assign_rule [ 1 ] :
                    next_state.append ( rp )
                for rn in can_assign_rule [ 2 ] :
                    next_state.append ( rn )
                next_state.append ( can_assign_rule [ 0 ] )
        # test if fixed point is reached
        if next_state == previous_state :
            fixed_point_reached = True
        # update the previous state with the actual one
        previous_state = next_state
    # delete duplicates from the fixed point
    next_state = list ( dict.fromkeys ( next_state ) )
    # delete the roles in R \ S∗
    roles = next_state
    # remove from CA all the rules that assign a role in R \ S*
    removed_can_assign_rules = [ ]
    for can_assign_rule in can_assign_rules :
        # structure ( ra , Rp , Rn , rt ) ∈ CA, so if rt in roles
        if can_assign_rule [ -1 ] in roles :
            removed_can_assign_rules.append ( can_assign_rule )
    can_assign_rules = removed_can_assign_rules
    # remove from CR all the rules that revoke a role in R \ S*
    removed_can_revoke_rule = [ ]
    for can_revoke_rule in can_revoke_rules :
        # structure (ra,rt) ∈ CR, so if rt in roles
        if can_revoke_rule [ -1 ] in roles :
            removed_can_revoke_rule.append ( can_revoke_rule )
    can_revoke_rules = removed_can_revoke_rule
    # return the sets of can assign rules and can revoke rules
    return can_assign_rules , can_revoke_rules

# function used to check if at least one user has the goal role
def check_if_at_least_one_user_has_goal_state ( lists_of_user_role_to_check , goal ) :
    # for each list of user-role assignments
    for list_of_user_role_to_check in lists_of_user_role_to_check :
        # for each user-role assignment in the actual list
        for user_role in list_of_user_role_to_check :
            # structure of user role= (user, role)
            # check if the role of the actual user role pair is equal to the goal role
            if user_role [ 1 ] == goal :
                return True
    # no user with the goal rule
    return False

# function used to get the set of users that have the target role of a can revoke rule
def user_with_target_can_revoke_rule ( can_revoke_rule , user_roles ) :
    # list to contain the set of users that have the target role
    users_with_target_role = [ ]
    # structure of can revoke rule:  (ra,rt) ∈ CR
    # for each user role pair
    for user_role in user_roles :
        # structure of user role: (user, role)
        # if the actual user has the role that is in the rt part of the revoke rule
        if user_role [ 1 ] == can_revoke_rule [ 1 ] :
            # add the actual user in the list of users that each of these has the target role
            users_with_target_role.append ( user_role [ 0 ] )
    # return the list of users with the target role
    return users_with_target_role

# function used to get the set of users that can receive the role rt using the can assign rule
def user_with_target_can_assign_rule ( can_assign_rule , user_roles ) :
    # initialize the list of possible users that can receive the role rt as empty list
    user_with_possible_role_rt = [ ]
    # create the list of roles for each user
    # example {'user0': ['Admin'], 'user1': ['Doctor']....}
    roles_each_user = model_users_roles ( user_roles )
    # for each user role
    for user_role in roles_each_user :
        # we must check 3 conditions: Rp ⊆ UR(ut) and Rn ∩ UR(ut) = ∅ and not( rt ∈ UR(ut) )
        if all ( item in roles_each_user [ user_role ] for item in can_assign_rule [ 1 ] ) :
            # if length of intersection between rn and roles is equal to 0 -> empty intersection
            if len ( [ value for value in roles_each_user [ user_role ] if value in can_assign_rule [ 2 ] ] ) == 0 :
                # if rt not in roles of actual user
                if not can_assign_rule [ -1 ] in roles_each_user [ user_role ] :
                    # i can add the user into the list
                    user_with_possible_role_rt.append ( user_role )
    # return the list of users that can receive the role rt
    return user_with_possible_role_rt

# function to set the variables for the actual file execution
def variables_actual_file_execution ( i ) :
    # import time to manage the timeout
    import time
    # calculate the maximum time from the actual time before starting the execution and the maximum time for execution equal to 5 seconds
    maximum_time = time.asctime ( time.localtime ( time.time ( ) + 5 ) )
    # set that we haven't found the flag for the actual file
    actual_flag_found = False
    # create the string for the actual file
    file = "policies/policy" + str ( i ) + ".arbac"
    return maximum_time , actual_flag_found , file

# create the string for the flag
flag = ""

# for each file in the folder policy
for i in range ( 1 , 9 ) :
    # variables for the actual round of execution as maximum time that in case it terminates, the flag found set equal false and the name of actual file
    maximum_time , actual_flag_found , file = variables_actual_file_execution ( i )
    # read the input file and obtain all parts
    roles , users , user_roles , can_revoke_rules , can_assign_rules , goal = parser_file ( file )
    # apply the backward slicing algorithm
    can_assign_rules , can_revoke_rules = backward_slicing ( goal , can_assign_rules , can_revoke_rules )
    # there can be more path that we want to control to reach the final goal and i initialize it with the input file content
    checkable_user_roles = [ user_roles ]
    # user role assignment list already seen initialized as empty list
    track_user_roles = [ ]
    # while not final state is reached and the time for execution is not finished
    while not actual_flag_found :
        # initialize the newest chekable user roles as empty list
        newest_checkable_user_roles = [ ]
        # for each checkable user role in the list of list of possible user role pair
        for checkable_user_role in checkable_user_roles :
            
            # create the list of possible user-target from the list of possible user that can get the actual role
            user_target_to_add = [ ]
            # for each can assign rule
            for can_assign_rule in can_assign_rules :
                # detect the users that i can associate the actual role
                user_actual_role = user_with_target_can_assign_rule ( can_assign_rule , checkable_user_role )
                # for each user in the list that they can receive the actual role
                for user in user_actual_role :
                    # create the list of user-roles to add to the list example user-target
                    user_target_to_add.append ( [ user , can_assign_rule [ -1 ] ] )
            
            # for each user-target entry
            for user_target in user_target_to_add :
                # create a copy of the actual user role list
                updated_possible_track = checkable_user_role.copy ( )
                # append the actual user target to the object copy
                updated_possible_track.append ( user_target )
                # if the new list is not in the list of all user-role track
                if updated_possible_track not in track_user_roles :
                    # i save the actual list to the newest object list copy
                    newest_checkable_user_roles.append ( updated_possible_track )
                    # i save the actual list to the list of already visited list
                    track_user_roles.append ( updated_possible_track )
            
            # create the list of possible user-target from the list of possible user that have the actual role
            user_roles_to_revoke = [ ]
            # for each can revoke rule
            for can_revoke_rule in can_revoke_rules :
                # the set of users that have the target role of the actual can revoke rule
                user_with_target_role = user_with_target_can_revoke_rule ( can_revoke_rule , checkable_user_role )
                # for each user that has the target role of the can revoke rule
                for user in user_with_target_role :
                    # create the list of user-roles to add to the list example user-target
                    user_roles_to_revoke.append ( [ user , can_revoke_rule [ -1 ] ] )
            
            # for each user-role pair in the list calculated before
            for user_role in user_roles_to_revoke :
                # create a copy of the actual user role list
                updated_possible_track = checkable_user_role.copy ( )
                # remove from the newest copy the actual user-role pair
                updated_possible_track.remove ( user_role )
                # if the new list is not in the list of all user-role track
                if updated_possible_track not in track_user_roles :
                    # i save the actual list to the newest object list copy
                    newest_checkable_user_roles.append ( updated_possible_track )
                    # i save the actual list to the list of already visited list
                    track_user_roles.append ( updated_possible_track )

            # update the list of list of possible user-role to check
            checkable_user_roles = newest_checkable_user_roles
            
            # if the final role is reached
            if check_if_at_least_one_user_has_goal_state ( checkable_user_roles , goal ) :
                # save one for the actual bit in the flag
                flag = flag + "1"
                # actual flag found
                actual_flag_found = True
                # go to the next file
                break

            # import time to use it for the timer
            import time
            
            # if the time to complete the actual execution is finished
            if time.asctime ( time.localtime ( time.time ( ) ) ) > maximum_time :
                # save zero for the actual bit in the flag
                flag = flag + "0"
                # actual flag found
                actual_flag_found = True
                # go to the next file
                break

# print the final flag
print ( "The final flag is: " + flag )
