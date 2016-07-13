Scenario: a position is equal to another position at the same place
Given the position 10, 10
When I compare to position 10, 10
Then the positions are equal
And it is not before the first position
And it is not after the first position

Scenario: a position is after another position
Given the position 10, 10
When I compare to position 20, 20
Then it is after the first position
And the positions are not equal
And it is not before the first position

Scenario: a position is directly after another position
Given the position 10, 10
When I compare to position 10, 11
Then it is after the first position
And the positions are not equal
And it is not before the first position

Scenario: a position is before another position
Given the position 10, 10
When I compare to position 5, 5
Then it is before the first position
And the positions are not equal
And it is not after the first position

Scenario: a position is directly before another position
Given the position 10, 10
When I compare to position 10, 9
Then it is before the first position
And the positions are not equal
And it is not after the first position

Scenario: a range is equal to another range
Scenario: a range is before a position
Scenario: a range is after a position
Scenario: a range is contained in another range

