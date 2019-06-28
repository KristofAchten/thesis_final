This repository contains the fully verified codebase of the case study that was discussed in my master's thesis on formally verifying the data race freedom property for [FreeRTOS](https://www.freertos.org/) based applications using the [VeriFast program verifier](https://people.cs.kuleuven.be/~bart.jacobs/verifast/).

# Case study folder
This folder contains the verified case study as it was discussed in chapter 4 of the thesis, found in the `casestudy_annotated.c` file. Additionally, the specifications for the used FreeRTOS APIs can be found in the `dependencies` subfolder. 

# Generalizations folder
This folder contains the generalized specifications for the different resource management APIs of FreeRTOS. Additionally, the case study as discussed in chapter 4 has been reverified with these generalized specifications, for which the solution can be found in the `casestudy_generalized.c` file. These generalizations were the topic of chapter 5 of the thesis.
