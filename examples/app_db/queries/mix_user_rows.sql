SELECT
  left_user.status AS left_status,
  right_user.display_name AS right_display_name
FROM app.users AS left_user
CROSS JOIN app.users AS right_user
WHERE left_user.email = $1
  AND right_user.email = $2;
